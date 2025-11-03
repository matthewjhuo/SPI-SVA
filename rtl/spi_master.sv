// SPI Master Controller
module spi_master (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       enable,
    input  wire       cpol,
    input  wire       cpha,
    input  wire [7:0] clkdiv,
    input  wire [7:0] tx_data,
    input  wire       tx_valid,
    output reg  [7:0] rx_data,
    output reg        busy,
    output reg        sclk,
    output reg        cs_n,
    output reg        mosi,
    input  wire       miso
);

    // State machine states
    parameter [1:0] IDLE = 2'b00;
    parameter [1:0] SETUP = 2'b01;
    parameter [1:0] TRANSFER = 2'b10;
    parameter [1:0] COMPLETE = 2'b11;

    reg [1:0]  state;
    reg [7:0]  shift_reg;
    reg [2:0]  bit_count;
    reg [7:0]  clk_count;
    
    // Clock generation
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_count <= 8'h0;
            sclk <= cpol;
        end else if (busy) begin
            if (clk_count == clkdiv) begin
                clk_count <= 8'h0;
                sclk <= ~sclk;
            end else begin
                clk_count <= clk_count + 1;
            end
        end else begin
            sclk <= cpol;
        end
    end

    // Main state machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            busy <= 1'b0;
            cs_n <= 1'b1;
            mosi <= 1'b0;
            rx_data <= 8'h0;
            shift_reg <= 8'h0;
            bit_count <= 3'h0;
        end else begin
            case (state)
                IDLE: begin
                    if (enable && tx_valid) begin
                        state <= SETUP;
                        busy <= 1'b1;
                        cs_n <= 1'b0;
                        shift_reg <= tx_data;
                        bit_count <= 3'h7;
                    end
                end

                SETUP: begin
                    state <= TRANSFER;
                    mosi <= shift_reg[7];
                end

                TRANSFER: begin
                    if (clk_count == clkdiv) begin
                        if (bit_count == 0) begin
                            state <= COMPLETE;
                        end else begin
                            bit_count <= bit_count - 1;
                            shift_reg <= {shift_reg[6:0], miso};
                            mosi <= shift_reg[6];
                        end
                    end
                end

                COMPLETE: begin
                    state <= IDLE;
                    busy <= 1'b0;
                    cs_n <= 1'b1;
                    rx_data <= {shift_reg[6:0], miso};
                end

                default: begin
                    state <= IDLE;
                end
            endcase
        end
    end

endmodule
