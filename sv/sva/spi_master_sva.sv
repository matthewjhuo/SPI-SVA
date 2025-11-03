`timescale 1ns/1ps

import spi_sva_pkg::*;

// Master 專用 SVA：
// - Master 負責產生 SCLK 與 CS_n，且不得驅動 MISO
// - 於變化沿更新 MOSI，於取樣沿保持 MOSI 穩定
// - CS 高時 SCLK 應保持 CPOL 閒置電平
module spi_master_sva #(parameter bit CPOL = 1'b0,
                        parameter bit CPHA = 1'b0,
                        parameter int unsigned DATA_WIDTH = 8,
                        parameter bit MSB_FIRST = 1'b1)
(
    spi_if #(CPOL, CPHA, DATA_WIDTH, MSB_FIRST) sif
);

    // 邊沿偵測（以系統 clk 同步）
    logic sclk_q;
    logic sclk_rise, sclk_fall;
    always @(posedge sif.clk or negedge sif.reset_n) begin
        if (!sif.reset_n) sclk_q <= CPOL; else sclk_q <= sif.sclk;
    end
    assign sclk_rise = (sif.sclk == 1'b1) && (sclk_q == 1'b0);
    assign sclk_fall = (sif.sclk == 1'b0) && (sclk_q == 1'b1);

    wire sampling_edge = is_sampling_edge(CPOL, CPHA, sclk_rise, sclk_fall);
    wire change_edge   = is_change_edge(CPOL, CPHA, sclk_rise, sclk_fall);

    // 1) CS 高時 SCLK 維持閒置且不切換
    property sclk_idle_when_cs_high;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (sif.cb.cs_n && $stable(sif.cb.cs_n)) |-> (sif.cb.sclk == CPOL && $stable(sif.cb.sclk));
    endproperty
    assert property (sclk_idle_when_cs_high)
        else $error("MASTER: SCLK toggles or not idle when CS_n is high");

    // 2) MOSI 在取樣沿穩定
    property mosi_stable_on_sampling_edge;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && sampling_edge) |-> $stable(sif.cb.mosi);
    endproperty
    assert property (mosi_stable_on_sampling_edge)
        else $error("MASTER: MOSI changes on sampling edge");

    // 3) MOSI 僅於變化沿切換（寬鬆為 warning）
    property mosi_changes_only_on_change_edges;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && !$stable(sif.cb.mosi)) |-> change_edge;
    endproperty
    assert property (mosi_changes_only_on_change_edges)
        else $warning("MASTER: MOSI toggled not on expected change edge");

    // 4) Master 不得驅動 MISO（需由 TB 標記 miso_is_driven 來源，或於實作中視為從屬）
    property master_never_drives_miso;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            1 |-> !sif.cb.miso_is_driven;
    endproperty
    // 此條件在多從裝置匯流排可能需要以階層性訊號區分，預設為 warning
    assert property (master_never_drives_miso)
        else $warning("MASTER: MISO should not be driven by master");

endmodule


