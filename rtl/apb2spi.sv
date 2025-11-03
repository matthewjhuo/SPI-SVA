// APB to SPI Bridge
module apb2spi (
    // APB Interface
    input  wire        pclk,
    input  wire        presetn,
    input  wire [31:0] paddr,
    input  wire        psel,
    input  wire        penable,
    input  wire        pwrite,
    input  wire [31:0] pwdata,
    output reg  [31:0] prdata,
    output wire        pready,
    output reg         pslverr,
    
    // SPI Interface
    output wire        spi_sclk,
    output wire        spi_cs_n,
    output wire        spi_mosi,
    input  wire        spi_miso
);

    // Internal registers
    reg  [7:0]  ctrl_reg;    // Control register
    reg  [7:0]  status_reg;  // Status register
    reg  [7:0]  tx_reg;      // Transmit register
    reg  [7:0]  clkdiv_reg;  // Clock divider register
    wire [7:0]  rx_data;     // Receive data
    wire        busy;        // SPI busy flag

    // SPI Master instance
    spi_master spi_master_inst (
        .clk      (pclk),
        .rst_n    (presetn),
        .enable   (ctrl_reg[0]),
        .cpol     (ctrl_reg[1]),
        .cpha     (ctrl_reg[2]),
        .clkdiv   (clkdiv_reg),
        .tx_data  (tx_reg),
        .tx_valid (1'b1),
        .rx_data  (rx_data),
        .busy     (busy),
        .sclk     (spi_sclk),
        .cs_n     (spi_cs_n),
        .mosi     (spi_mosi),
        .miso     (spi_miso)
    );

    // APB write decoder
    wire write_ctrl   = psel && penable && pwrite && (paddr[3:0] == 4'h0);
    wire write_tx     = psel && penable && pwrite && (paddr[3:0] == 4'h8);
    wire write_clkdiv = psel && penable && pwrite && (paddr[3:0] == 4'hC);

    // APB write logic
    always @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            ctrl_reg   <= 8'h0;
            tx_reg     <= 8'h0;
            clkdiv_reg <= 8'h8;
            pslverr    <= 1'b0;
        end else begin
            if (write_ctrl)   ctrl_reg   <= pwdata[7:0];
            if (write_tx)     tx_reg     <= pwdata[7:0];
            if (write_clkdiv) clkdiv_reg <= pwdata[7:0];
            pslverr <= psel && penable && pwrite && !write_ctrl && !write_tx && !write_clkdiv;
        end
    end

    // APB read logic
    reg [31:0] read_data;
    always @(*) begin
        case (paddr[3:0])
            4'h0: read_data = {24'h0, ctrl_reg};
            4'h4: read_data = {24'h0, status_reg};
            4'h8: read_data = {24'h0, rx_data};
            4'hC: read_data = {24'h0, clkdiv_reg};
            default: read_data = 32'h0;
        endcase
    end

    always @(posedge pclk or negedge presetn) begin
        if (!presetn)
            prdata <= 32'h0;
        else if (psel && !pwrite)
            prdata <= read_data;
    end

    // Status register update
    always @(posedge pclk or negedge presetn) begin
        if (!presetn)
            status_reg <= 8'h0;
        else
            status_reg <= {7'h0, busy};
    end

    // Always ready
    assign pready = 1'b1;

endmodule
