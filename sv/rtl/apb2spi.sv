`timescale 1ns/1ps

// 簡化 APB3 -> SPI Master 控制器
// - APB3 寫入控制暫存器以設定 CPOL/CPHA/位序/分頻與資料
// - 透過 CMD.start 觸發一次 DATA_WIDTH 位的傳輸
// - 以 clock divider 產生 SCLK，依 CPOL/CPHA 決定取樣/變化沿
// - 以 spi_if 連接外部 SPI 匯流排（master 驅動 sclk/cs_n/mosi，接收 miso）

import spi_sva_pkg::*;

module apb2spi #(
    parameter int unsigned DATA_WIDTH_DEFAULT = 8,
    parameter bit          MSB_FIRST_DEFAULT = 1'b1
)(
    // APB3
    input  logic        pclk,
    input  logic        presetn,
    input  logic        psel,
    input  logic        penable,
    input  logic        pwrite,
    input  logic [7:0]  paddr,
    input  logic [31:0] pwdata,
    output logic [31:0] prdata,
    output logic        pready,
    output logic        pslverr,

    // System observation clock/reset for SVA must align with interface
    spi_if              sif
);

    // 寄存器映射（簡化示例）
    // 0x00 CTRL: [0]en [1]cpol [2]cpha [3]msb_first [15:8]data_width_minus1
    // 0x04 DIV:  分頻值（SCLK = pclk/(2*(DIV+1))）
    // 0x08 TX:   待發送資料（最低 DATA_WIDTH bits 有效）
    // 0x0C RX:   接收資料（只讀）
    // 0x10 CMD:  [0]start [8]keep_cs_low（保持選取，示例未用於多字節）
    // 0x14 STS:  [0]busy [1]done (自清) [2]rx_valid (自清讀)

    // CTRL
    logic ctrl_en, ctrl_cpol, ctrl_cpha, ctrl_msb_first;
    logic [7:0] ctrl_dw_m1; // DATA_WIDTH-1
    // DIV
    logic [15:0] div;
    // TX/RX
    logic [31:0] tx_reg, rx_reg;
    // CMD
    logic cmd_start;
    logic cmd_keep_cs_low;
    // STS
    logic sts_busy, sts_done, sts_rx_valid;

    // APB read mux
    always_comb begin
        prdata = '0;
        unique case (paddr[7:2])
            6'h00: prdata = {16'b0, 8'(ctrl_dw_m1), 4'b0, ctrl_msb_first, ctrl_cpha, ctrl_cpol, ctrl_en};
            6'h01: prdata = {16'b0, div};
            6'h02: prdata = tx_reg;
            6'h03: prdata = rx_reg;
            6'h04: prdata = {30'b0, cmd_keep_cs_low, 1'b0};
            6'h05: prdata = {29'b0, sts_rx_valid, sts_done, sts_busy};
            default: prdata = '0;
        endcase
    end

    // APB write
    wire apb_write = psel & penable & pwrite;
    wire apb_read  = psel & penable & ~pwrite;
    assign pready  = psel; // 零等待示例
    assign pslverr = 1'b0;

    // 寫入/讀出副作用
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            ctrl_en        <= 1'b0;
            ctrl_cpol      <= 1'b0;
            ctrl_cpha      <= 1'b0;
            ctrl_msb_first <= MSB_FIRST_DEFAULT;
            ctrl_dw_m1     <= DATA_WIDTH_DEFAULT-1;
            div            <= 16'd1;
            tx_reg         <= '0;
            cmd_start      <= 1'b0;
            cmd_keep_cs_low<= 1'b0;
            sts_done       <= 1'b0;
            sts_rx_valid   <= 1'b0;
        end else begin
            // default self-clear
            if (cmd_start) cmd_start <= 1'b0;
            if (sts_done)  sts_done  <= 1'b0;
            
            if (apb_write) begin
                unique case (paddr[7:2])
                    6'h00: begin
                        ctrl_en        <= pwdata[0];
                        ctrl_cpol      <= pwdata[1];
                        ctrl_cpha      <= pwdata[2];
                        ctrl_msb_first <= pwdata[3];
                        ctrl_dw_m1     <= pwdata[15:8];
                    end
                    6'h01: div    <= pwdata[15:0];
                    6'h02: tx_reg <= pwdata;
                    6'h04: begin
                        cmd_start       <= pwdata[0];
                        cmd_keep_cs_low <= pwdata[8];
                    end
                    default: ;
                endcase
            end

            if (apb_read && paddr[7:2] == 6'h03) begin
                sts_rx_valid <= 1'b0; // read-clear
            end
        end
    end

    // SPI 引擎
    localparam int CNTW = 16;
    logic [CNTW-1:0] div_cnt;
    logic sclk_tick; // 產生 SCLK 半週期切換訊號

    // 接口連接
    // SVA 觀測時脈/重設與 APB 對齊
    assign sif.clk     = pclk;
    assign sif.reset_n = presetn;

    // CS/SCLK 初值
    // 注意：sif.sclk/sif.cs_n/sif.mosi 為介面內邏輯，直接賦值
    // 主控應確保非選取時 SCLK 處於 CPOL 閒置

    // 時脈分頻
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            div_cnt   <= '0;
            sclk_tick <= 1'b0;
        end else if (sts_busy && ctrl_en) begin
            if (div_cnt == div) begin
                div_cnt   <= '0;
                sclk_tick <= 1'b1;
            end else begin
                div_cnt   <= div_cnt + 1'b1;
                sclk_tick <= 1'b0;
            end
        end else begin
            div_cnt   <= '0;
            sclk_tick <= 1'b0;
        end
    end

    // 傳輸 FSM
    typedef enum logic [1:0] {IDLE, ASSERT_CS, SHIFT, DEASSERT_CS} state_e;
    state_e state, nstate;
    logic [7:0] bit_cnt; // 支援到 256 位（足夠常見應用）
    logic [31:0] shifter_tx, shifter_rx;

    wire [7:0] data_width = ctrl_dw_m1 + 8'd1;
    
    // 初值控制
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            state      <= IDLE;
            sts_busy   <= 1'b0;
            sif.cs_n   <= 1'b1;
            sif.sclk   <= 1'b0; // 將於 IDLE 維持為 CPOL
            sif.mosi   <= 1'b0;
            bit_cnt    <= '0;
            shifter_tx <= '0;
            shifter_rx <= '0;
        end else begin
            state <= nstate;

            // 預設在 IDLE 維持 SCLK = CPOL
            if (state == IDLE) begin
                sif.sclk <= ctrl_cpol;
            end

            case (state)
                IDLE: begin
                    sts_busy <= 1'b0;
                    if (psel && penable && pwrite && paddr[7:2]==6'h04 && pwdata[0] && ctrl_en) begin
                        // 同步起始：捕捉 TX/參數
                        shifter_tx <= tx_reg;
                        shifter_rx <= '0;
                        bit_cnt    <= 8'd0;
                        sts_busy   <= 1'b1;
                    end
                end
                ASSERT_CS: begin
                    // 保持 SCLK idle level，並拉低 CS
                    sif.cs_n <= 1'b0;
                    sif.sclk <= ctrl_cpol;
                    // 在 CPHA 決定的變化沿前，先準備第一個 MOSI 位元
                    if (bit_cnt == 0) begin
                        logic next_bit;
                        next_bit = ctrl_msb_first ? shifter_tx[data_width-1] : shifter_tx[0];
                        sif.mosi <= next_bit;
                    end
                end
                SHIFT: begin
                    // 以 sclk_tick 切換 sclk，並依 CPOL/CPHA 進行 change/sample
                    if (sclk_tick) begin
                        // 產生半週期切換
                        sif.sclk <= ~sif.sclk;
                        // 邊沿分類（相對於 CPOL/CPHA）需以實際 rise/fall 判斷
                        bit sclk_is_rise = (sif.sclk == 1'b1);
                        bit sample_edge  = is_sampling_edge(ctrl_cpol, ctrl_cpha, sclk_is_rise, ~sclk_is_rise);
                        bit change_edge  = is_change_edge  (ctrl_cpol, ctrl_cpha, sclk_is_rise, ~sclk_is_rise);

                        if (!sif.cs_n && sample_edge) begin
                            // 取樣 MISO
                            if (ctrl_msb_first)
                                shifter_rx <= {shifter_rx[30:0], sif.miso};
                            else
                                shifter_rx <= {sif.miso, shifter_rx[31:1]};
                            bit_cnt <= bit_cnt + 1'b1;
                        end

                        if (!sif.cs_n && change_edge) begin
                            // 準備下一個 MOSI 位
                            logic [31:0] tmp = shifter_tx;
                            if (ctrl_msb_first) begin
                                tmp <= {tmp[30:0], 1'b0};
                            end else begin
                                tmp <= {1'b0, tmp[31:1]};
                            end
                            shifter_tx <= tmp;
                            logic next_bit;
                            next_bit = ctrl_msb_first ? tmp[data_width-1] : tmp[0];
                            sif.mosi <= next_bit;
                        end
                    end
                end
                DEASSERT_CS: begin
                    sif.cs_n <= 1'b1;
                    sif.sclk <= ctrl_cpol;
                end
            endcase

            // 完成處理
            if (state == SHIFT && bit_cnt == data_width) begin
                rx_reg      <= shifter_rx;
                sts_done    <= 1'b1;
                sts_rx_valid<= 1'b1;
            end
        end
    end

    // next-state 決定
    always_comb begin
        nstate = state;
        unique case (state)
            IDLE: begin
                if (sts_busy) nstate = ASSERT_CS;
            end
            ASSERT_CS: begin
                // 進入 SHIFT（等待一個分頻 tick 以開始切換）
                nstate = SHIFT;
            end
            SHIFT: begin
                if (bit_cnt == data_width) nstate = DEASSERT_CS;
            end
            DEASSERT_CS: begin
                nstate = IDLE;
            end
        endcase
    end

endmodule


