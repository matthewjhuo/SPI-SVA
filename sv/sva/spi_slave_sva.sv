`timescale 1ns/1ps

import spi_sva_pkg::*;

// Slave 專用 SVA：
// - 只在被選取（CS_n==0）時才允許驅動 MISO
// - 於主裝置取樣沿前保持 MISO 穩定（在取樣沿當下不可翻轉）
// - 不得驅動 SCLK/CS_n（由主裝置控制）
module spi_slave_sva #(parameter bit CPOL = 1'b0,
                       parameter bit CPHA = 1'b0,
                       parameter int unsigned DATA_WIDTH = 8,
                       parameter bit MSB_FIRST = 1'b1)
(
    spi_if #(CPOL, CPHA, DATA_WIDTH, MSB_FIRST) sif
);

    logic sclk_q;
    logic sclk_rise, sclk_fall;
    always @(posedge sif.clk or negedge sif.reset_n) begin
        if (!sif.reset_n) sclk_q <= CPOL; else sclk_q <= sif.sclk;
    end
    assign sclk_rise = (sif.sclk == 1'b1) && (sclk_q == 1'b0);
    assign sclk_fall = (sif.sclk == 1'b0) && (sclk_q == 1'b1);

    wire sampling_edge = is_sampling_edge(CPOL, CPHA, sclk_rise, sclk_fall);
    wire change_edge   = is_change_edge(CPOL, CPHA, sclk_rise, sclk_fall);

    // 1) 只有在 CS 低時才允許驅動 MISO
    property miso_drive_only_when_selected;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n) |-> sif.cb.miso_is_driven;
    endproperty
    assert property (miso_drive_only_when_selected)
        else $error("SLAVE: MISO must be driven only when CS_n is low");

    property miso_not_driven_when_cs_high;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (sif.cb.cs_n) |-> !sif.cb.miso_is_driven;
    endproperty
    assert property (miso_not_driven_when_cs_high)
        else $error("SLAVE: MISO driven while CS_n is high");

    // 2) 取樣沿當下 MISO 穩定（避免在主裝置取樣瞬間改變）
    property miso_stable_on_sampling_edge;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && sampling_edge) |-> $stable(sif.cb.miso);
    endproperty
    assert property (miso_stable_on_sampling_edge)
        else $error("SLAVE: MISO changes on master's sampling edge");

    // 3) Slave 不應驅動 SCLK/CS（無法直接斷言，改以警告：SCLK/CS 應視為外部）
    // 若有階層性訊號可判斷驅動者，可補強此檢查。

endmodule


