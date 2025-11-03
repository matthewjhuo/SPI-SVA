`timescale 1ns/1ps

import spi_sva_pkg::*;

// Monitor（被動監測）專用 SVA：
// - 通用協定規則（SCLK 閒置、frame 位數、毛刺防護、MOSI 取樣/變化邊界等）
// - 不假設驅動者，僅從介面觀測
module spi_monitor_sva #(parameter bit CPOL = 1'b0,
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

    // SCLK 閒置於 CS 高
    property sclk_idle_when_cs_high;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (sif.cb.cs_n && $stable(sif.cb.cs_n)) |-> (sif.cb.sclk == CPOL && $stable(sif.cb.sclk));
    endproperty
    assert property (sclk_idle_when_cs_high)
        else $error("MON: SCLK toggles or not idle when CS_n is high");

    // frame 位數計數（取樣沿計數）
    logic [$clog2(4096)-1:0] bit_count;
    always @(posedge sif.clk or negedge sif.reset_n) begin
        if (!sif.reset_n) bit_count <= '0;
        else if (sif.cs_n) bit_count <= '0;
        else if (sampling_edge) bit_count <= bit_count + 1'b1;
    end

    property frame_bitcount_equals_width;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            $fell(sif.cb.cs_n) |-> ##[1:$] $rose(sif.cb.cs_n) and (bit_count == DATA_WIDTH);
    endproperty
    assert property (frame_bitcount_equals_width)
        else $error("MON: frame bit count != DATA_WIDTH");

    // SCLK 毛刺防護（至少 1 個系統 clk 穩定）
    property sclk_no_glitch_under_cs_low;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && (sclk_rise || sclk_fall)) |-> ##1 $stable(sif.cb.sclk);
    endproperty
    assert property (sclk_no_glitch_under_cs_low)
        else $error("MON: SCLK glitch detected under CS low");

    // MOSI 取樣沿穩定
    property mosi_stable_on_sampling_edge;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && sampling_edge) |-> $stable(sif.cb.mosi);
    endproperty
    assert property (mosi_stable_on_sampling_edge)
        else $error("MON: MOSI changes on sampling edge");

    // MOSI 變化沿切換（寬鬆警告）
    property mosi_changes_only_on_change_edges;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && !$stable(sif.cb.mosi)) |-> change_edge;
    endproperty
    assert property (mosi_changes_only_on_change_edges)
        else $warning("MON: MOSI toggled not on expected change edge");

endmodule


