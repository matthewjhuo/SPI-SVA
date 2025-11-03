// spi_sva: Assertions for SPI protocol (CPOL/CPHA modes, frame/CS rules, bit count, basic timing)

`timescale 1ns/1ps

package spi_sva_pkg;

  // Utility function: return 1 when edge is the sampling edge per CPOL/CPHA
  function automatic bit is_sampling_edge(
      bit cpol,
      bit cpha,
      bit sclk_rise,
      bit sclk_fall
  );
    bit sample_on_rise;
    // Mode mapping:
    // CPOL=0, CPHA=0 -> sample @ rising
    // CPOL=0, CPHA=1 -> sample @ falling
    // CPOL=1, CPHA=0 -> sample @ falling
    // CPOL=1, CPHA=1 -> sample @ rising
    sample_on_rise = (cpha == cpol);
    return sample_on_rise ? sclk_rise : sclk_fall;
  endfunction

  function automatic bit is_change_edge(
      bit cpol,
      bit cpha,
      bit sclk_rise,
      bit sclk_fall
  );
    // Change edge is the opposite of sampling edge
    return is_sampling_edge(cpol, cpha, sclk_fall, sclk_rise);
  endfunction

endpackage : spi_sva_pkg


import spi_sva_pkg::*;

// Bind module to an instance of spi_if
module spi_sva_bind #(parameter bit CPOL = 1'b0,
                      parameter bit CPHA = 1'b0,
                      parameter int unsigned DATA_WIDTH = 8,
                      parameter bit MSB_FIRST = 1'b1)
(
    spi_if #(CPOL, CPHA, DATA_WIDTH, MSB_FIRST) sif
);

    // Internal edge detection synced to cb clocking (system clk)
    logic sclk_q;
    logic sclk_rise, sclk_fall;

    always @(posedge sif.clk or negedge sif.reset_n) begin
        if (!sif.reset_n) begin
            sclk_q <= CPOL; // idle
        end else begin
            sclk_q <= sif.sclk;
        end
    end

    assign sclk_rise = (sif.sclk == 1'b1) && (sclk_q == 1'b0);
    assign sclk_fall = (sif.sclk == 1'b0) && (sclk_q == 1'b1);

    // 1) SCLK idle when CS high
    property sclk_idle_when_cs_high;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (sif.cb.cs_n && $stable(sif.cb.cs_n)) |-> (sif.cb.sclk == CPOL && $stable(sif.cb.sclk));
    endproperty
    assert property (sclk_idle_when_cs_high)
        else $error("SPI: SCLK toggles or not idle when CS_n is high");

    // 2) Count sampling edges within a frame equals DATA_WIDTH
    logic [$clog2(4096)-1:0] bit_count;
    wire sampling_edge = is_sampling_edge(CPOL, CPHA, sclk_rise, sclk_fall);
    wire change_edge   = is_change_edge(CPOL, CPHA, sclk_rise, sclk_fall);

    always @(posedge sif.clk or negedge sif.reset_n) begin
        if (!sif.reset_n) begin
            bit_count <= '0;
        end else begin
            if (sif.cs_n) begin
                bit_count <= '0;
            end else if (sampling_edge) begin
                bit_count <= bit_count + 1'b1;
            end
        end
    end

    property frame_bitcount_equals_width;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            $fell(sif.cb.cs_n) |-> ##[1:$] $rose(sif.cb.cs_n) and (bit_count == DATA_WIDTH);
    endproperty
    assert property (frame_bitcount_equals_width)
        else $error("SPI: frame bit count != DATA_WIDTH");

    // 3) During CS low, SCLK must not glitch shorter than 1 sys clk (basic integrity)
    property sclk_no_glitch_under_cs_low;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && (sclk_rise || sclk_fall)) |-> ##1 $stable(sif.cb.sclk);
    endproperty
    assert property (sclk_no_glitch_under_cs_low)
        else $error("SPI: SCLK glitch detected under CS low");

    // 4) MOSI stable at sampling edge (no toggle on the exact sampling cycle)
    property mosi_stable_on_sampling_edge;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && sampling_edge) |-> $stable(sif.cb.mosi);
    endproperty
    assert property (mosi_stable_on_sampling_edge)
        else $error("SPI: MOSI changes on sampling edge");

    // 5) MOSI changes only on change edges (optional lenient check)
    property mosi_changes_only_on_change_edges;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (!sif.cb.cs_n && !$stable(sif.cb.mosi)) |-> change_edge;
    endproperty
    assert property (mosi_changes_only_on_change_edges)
        else $warning("SPI: MOSI toggled not on expected change edge");

    // 6) MISO not driven when CS high (requires TB to drive miso_is_driven)
    property miso_not_driven_when_cs_high;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            (sif.cb.cs_n) |-> !sif.cb.miso_is_driven;
    endproperty
    assert property (miso_not_driven_when_cs_high)
        else $error("SPI: MISO driven while CS_n is high");

    // 7) SCLK idle level equals CPOL when CS goes high
    property sclk_returns_to_idle_on_cs_release;
        @(posedge sif.clk) disable iff (!sif.reset_n)
            $rose(sif.cb.cs_n) |-> (sif.cb.sclk == CPOL);
    endproperty
    assert property (sclk_returns_to_idle_on_cs_release)
        else $error("SPI: SCLK not at idle level on CS release");

    // Covergroups
    covergroup cg_mode @(posedge sif.clk);
        coverpoint {CPOL, CPHA} {
            bins mode0 = {2'b00};
            bins mode1 = {2'b01};
            bins mode2 = {2'b10};
            bins mode3 = {2'b11};
        }
        coverpoint DATA_WIDTH { bins w4 = {4}; bins w8 = {8}; bins w16 = {16}; bins others = default; }
        coverpoint MSB_FIRST { bins msb = {1}; bins lsb = {0}; }
    endgroup

    cg_mode u_cg_mode = new();

endmodule : spi_sva_bind


