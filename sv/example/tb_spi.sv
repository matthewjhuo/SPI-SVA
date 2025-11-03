`timescale 1ns/1ps

import spi_sva_pkg::*;

module tb_spi;
    // System clock/reset for SVA observation
    logic clk;
    logic reset_n;

    // Parameters for this test
    localparam bit CPOL = 1'b0;
    localparam bit CPHA = 1'b0; // Try changing to 1 to test Mode1, etc.
    localparam int unsigned DATA_WIDTH = 8;
    localparam bit MSB_FIRST = 1'b1;

    // Interface
    spi_if #(CPOL, CPHA, DATA_WIDTH, MSB_FIRST) sif (.clk(clk), .reset_n(reset_n));

    // Simple clock
    initial clk = 0;
    always #5 clk = ~clk; // 100MHz

    // APB bus signals
    logic        psel, penable, pwrite;
    logic [7:0]  paddr;
    logic [31:0] pwdata;
    logic [31:0] prdata;
    logic        pready;
    logic        pslverr;

    // DUT: APB2SPI
    apb2spi u_dut (
        .pclk    (clk),
        .presetn (reset_n),
        .psel    (psel),
        .penable (penable),
        .pwrite  (pwrite),
        .paddr   (paddr),
        .pwdata  (pwdata),
        .prdata  (prdata),
        .pready  (pready),
        .pslverr (pslverr),
        .sif     (sif)
    );

    // APB helpers
    task automatic apb_write(input [7:0] addr, input [31:0] data);
        @(posedge clk);
        psel <= 1; penable <= 0; pwrite <= 1; paddr <= addr; pwdata <= data;
        @(posedge clk);
        penable <= 1;
        @(posedge clk);
        psel <= 0; penable <= 0; pwrite <= 0; pwdata <= '0; paddr <= '0;
    endtask

    task automatic apb_read(input [7:0] addr, output [31:0] data);
        @(posedge clk);
        psel <= 1; penable <= 0; pwrite <= 0; paddr <= addr;
        @(posedge clk);
        penable <= 1;
        @(posedge clk);
        data = prdata;
        psel <= 0; penable <= 0; paddr <= '0;
    endtask

    // Simple slave stub: drives MISO only when selected
    // For illustration, echo MOSI delayed by half cycle (logic-only)
    initial begin
        sif.miso_is_driven = 1'b0;
        sif.miso = 'z;
        forever begin
            @(posedge clk);
            if (!reset_n) begin
                sif.miso_is_driven <= 1'b0;
                sif.miso <= 'z;
            end else if (!sif.cs_n) begin
                sif.miso_is_driven <= 1'b1;
                // Provide some deterministic value; here tie to MOSI
                sif.miso <= sif.mosi;
            end else begin
                sif.miso_is_driven <= 1'b0;
                sif.miso <= 'z;
            end
        end
    end

    // Reset and stimulus
    initial begin
        reset_n = 0;
        psel = 0; penable = 0; pwrite = 0; paddr = '0; pwdata = '0;
        // 初始 bus 靜止，介面由 DUT 駕馭
        repeat (5) @(posedge clk);
        reset_n = 1;

        // 設定 CTRL: en=1, CPOL/CPHA 依參數, MSB_FIRST, DATA_WIDTH
        apb_write(8'h00, {16'b0, DATA_WIDTH-1, 4'b0, MSB_FIRST, CPHA, CPOL, 1'b1});
        // 設定分頻（較慢時脈便於觀察）
        apb_write(8'h04, 32'd2);

        // 傳送 0xA5
        apb_write(8'h08, 32'h000000A5);
        apb_write(8'h10, 32'h1); // start
        // 等待 done
        automatic int guard = 0;
        automatic logic [31:0] sts;
        do begin
            apb_read(8'h14, sts);
            guard++;
        end while (!sts[1] && guard < 1000);

        // 傳送 0x3C
        apb_write(8'h08, 32'h0000003C);
        apb_write(8'h10, 32'h1);
        guard = 0;
        do begin
            apb_read(8'h14, sts);
            guard++;
        end while (!sts[1] && guard < 1000);

        // 讀 RX（清除 rx_valid）
        automatic logic [31:0] rx;
        apb_read(8'h0C, rx);
        apb_read(8'h0C, rx);

        repeat (20) @(posedge clk);
        $finish;
    end

    // Bind SVA：master / slave / monitor
    spi_master_sva #(.CPOL(CPOL), .CPHA(CPHA), .DATA_WIDTH(DATA_WIDTH), .MSB_FIRST(MSB_FIRST))
        u_spi_master_sva (.sif(sif));
    spi_slave_sva  #(.CPOL(CPOL), .CPHA(CPHA), .DATA_WIDTH(DATA_WIDTH), .MSB_FIRST(MSB_FIRST))
        u_spi_slave_sva  (.sif(sif));
    spi_monitor_sva#(.CPOL(CPOL), .CPHA(CPHA), .DATA_WIDTH(DATA_WIDTH), .MSB_FIRST(MSB_FIRST))
        u_spi_monitor_sva(.sif(sif));

endmodule


