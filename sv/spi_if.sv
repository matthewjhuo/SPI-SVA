interface spi_if #(
    parameter bit CPOL = 1'b0,
    parameter bit CPHA = 1'b0,
    parameter int unsigned DATA_WIDTH = 8,
    parameter bit MSB_FIRST = 1'b1
)(
    input  logic clk,
    input  logic reset_n
);

    // SPI signals
    logic sclk;
    logic cs_n;
    logic mosi;
    tri   miso;          // tri for potential high-Z observation in TB

    // Optional helper to detect if MISO is driven (from TB or slave model)
    logic miso_is_driven;

    // Derived edges for CPOL/CPHA meaning
    // For assertions, we observe sclk edges relative to CPOL/CPHA

    // Clocking block for stable sampling in SVA
    clocking cb @(posedge clk);
        input reset_n;
        input sclk, cs_n, mosi, miso, miso_is_driven;
    endclocking

endinterface : spi_if


