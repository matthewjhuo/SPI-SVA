// APB2SPI Testbench for Icarus Verilog
module apb2spi_tb;
    // Clock and Reset
    reg        pclk;
    reg        presetn;
    
    // APB Signals
    reg [31:0] paddr;
    reg        psel;
    reg        penable;
    reg        pwrite;
    reg [31:0] pwdata;
    wire [31:0] prdata;
    wire        pready;
    wire        pslverr;
    
    // SPI Signals
    wire        spi_sclk;
    wire        spi_cs_n;
    wire        spi_mosi;
    reg         spi_miso;

    // Clock generation
    initial begin
        pclk = 0;
        forever #5 pclk = ~pclk;
    end

    // DUT instantiation
    apb2spi dut (
        .pclk     (pclk),
        .presetn  (presetn),
        .paddr    (paddr),
        .psel     (psel),
        .penable  (penable),
        .pwrite   (pwrite),
        .pwdata   (pwdata),
        .prdata   (prdata),
        .pready   (pready),
        .pslverr  (pslverr),
        .spi_sclk (spi_sclk),
        .spi_cs_n (spi_cs_n),
        .spi_mosi (spi_mosi),
        .spi_miso (spi_miso)
    );

    // Waveform dumping for GTKWave
    initial begin
        $dumpfile("apb2spi_tb.vcd");
        $dumpvars(0, apb2spi_tb);
    end

    // APB Write task
    task apb_write;
        input [31:0] addr;
        input [31:0] data;
        begin
            @(posedge pclk);
            psel    <= 1'b1;
            pwrite  <= 1'b1;
            paddr   <= addr;
            pwdata  <= data;
            @(posedge pclk);
            penable <= 1'b1;
            @(posedge pclk);
            while (!pready) @(posedge pclk);
            psel    <= 1'b0;
            penable <= 1'b0;
        end
    endtask

    // APB Read task
    task apb_read;
        input [31:0] addr;
        output [31:0] data;
        begin
            @(posedge pclk);
            psel    <= 1'b1;
            pwrite  <= 1'b0;
            paddr   <= addr;
            @(posedge pclk);
            penable <= 1'b1;
            @(posedge pclk);
            while (!pready) @(posedge pclk);
            data    = prdata;
            psel    <= 1'b0;
            penable <= 1'b0;
        end
    endtask

    // Test scenario
    initial begin
        // Initialize signals
        presetn = 0;
        psel    = 0;
        penable = 0;
        pwrite  = 0;
        paddr   = 0;
        pwdata  = 0;
        spi_miso = 0;

        // Reset period
        #100 presetn = 1;

        // Configure SPI
        apb_write(32'h0, 32'h1);     // Enable SPI
        apb_write(32'hC, 32'h8);     // Set clock divider

        // Test case 1: Basic data transfer
        apb_write(32'h8, 32'hA5);    // Write data
        #1000;                        // Wait for transfer

        // Test case 2: Read status
        begin
            reg [31:0] status;
            apb_read(32'h4, status);
            $display("Status: %h", status);
        end
        
        // Test case 3: Multiple transfers
        begin
            integer i;
            for(i = 0; i < 4; i = i + 1) begin
                apb_write(32'h8, 32'h55 + i);
                #1000;
            end
        end

        // Test case 4: Clock polarity and phase
        apb_write(32'h0, 32'h7);     // Enable SPI, CPOL=1, CPHA=1
        apb_write(32'h8, 32'hFF);    // Write data
        #1000;

        // Test complete
        #1000;
        $finish;
    end

    // Monitor and finish
    initial begin
        // Setup monitoring
        $monitor("Time=%0t cs_n=%0b sclk=%0b mosi=%0b miso=%0b",
                 $time, spi_cs_n, spi_sclk, spi_mosi, spi_miso);
        
        // Maximum simulation time
        #10000 $finish;
    end

    // Handle potential simulation errors
    initial begin
        // Timeout watchdog
        #50000;
        $display("Error: Simulation timeout");
        $finish;
    end

endmodule
