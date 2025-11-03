// SPI Monitor Assertions
module spi_monitor_assertions (
    input  logic        clk,           // System Clock
    input  logic        rst_n,         // Active Low Reset
    input  logic        sclk,          // SPI Clock
    input  logic        cs_n,          // Chip Select (Active Low)
    input  logic        mosi,          // Master Out Slave In
    input  logic        miso,          // Master In Slave Out
    input  logic [7:0]  captured_mosi, // Captured MOSI data
    input  logic [7:0]  captured_miso  // Captured MISO data
);r Assertions
module spi_monitor_assertions
  import uvm_pkg::*;
(
  input  logic        clk,          // System Clock
  input  logic        rst_n,        // Active Low Reset
  input  logic        sclk,         // SPI Clock
  input  logic        cs_n,         // Chip Select (Active Low)
  input  logic        mosi,         // Master Out Slave In
  input  logic        miso,         // Master In Slave Out
  input  logic [7:0]  captured_mosi, // Captured MOSI data
  input  logic [7:0]  captured_miso  // Captured MISO data
);

  // Protocol Monitoring Properties
  property p_valid_transaction;
    @(posedge clk) $fell(cs_n) |-> ##[1:$] $rose(cs_n);
  endproperty

  // Clock Monitoring Properties
  property p_sclk_activity;
    @(posedge clk) !cs_n |-> ##[1:4] $changed(sclk);
  endproperty

  property p_sclk_idle;
    @(posedge clk) cs_n |-> !$changed(sclk);
  endproperty

  // Data Monitoring Properties
  property p_data_sampling;
    @(posedge sclk) !cs_n |-> (!$isunknown(mosi) && !$isunknown(miso));
  endproperty

  property p_data_capture_complete;
    @(posedge clk) $rose(cs_n) |-> (!$isunknown(captured_mosi) && !$isunknown(captured_miso));
  endproperty

  // Protocol Timing Properties
  property p_min_cs_high;
    @(posedge clk) $rose(cs_n) |-> ##[2:$] $fell(cs_n);
  endproperty

  property p_byte_alignment;
    logic [3:0] bit_count = 0;
    @(posedge sclk) (
      if (!cs_n) begin
        bit_count <= bit_count + 1;
        if (bit_count == 7)
          bit_count <= 0;
      end
      else
        bit_count <= 0
    );
  endproperty

  // Assert all properties
  a_valid_transaction:     assert property(p_valid_transaction)     
    else `uvm_error("MON_ASSERT", "Invalid SPI transaction");
  a_sclk_activity:        assert property(p_sclk_activity)        
    else `uvm_error("MON_ASSERT", "No SCLK activity during transfer");
  a_sclk_idle:           assert property(p_sclk_idle)           
    else `uvm_error("MON_ASSERT", "SCLK active when CS inactive");
  a_data_sampling:       assert property(p_data_sampling)       
    else `uvm_error("MON_ASSERT", "Invalid data sampling");
  a_data_capture_complete: assert property(p_data_capture_complete) 
    else `uvm_error("MON_ASSERT", "Data capture incomplete");
  a_min_cs_high:         assert property(p_min_cs_high)         
    else `uvm_error("MON_ASSERT", "CS high period too short");
  a_byte_alignment:      assert property(p_byte_alignment)      
    else `uvm_error("MON_ASSERT", "Byte alignment error");

  // Cover properties
  c_valid_transaction:     cover property(p_valid_transaction);
  c_sclk_activity:        cover property(p_sclk_activity);
  c_sclk_idle:           cover property(p_sclk_idle);
  c_data_sampling:       cover property(p_data_sampling);
  c_data_capture_complete: cover property(p_data_capture_complete);
  c_min_cs_high:         cover property(p_min_cs_high);
  c_byte_alignment:      cover property(p_byte_alignment);

  // 監控特殊情況
  sequence eight_bits_transfer;
    !cs_n ##1 (!cs_n && $changed(sclk))[8];
  endsequence

  property p_complete_byte;
    @(posedge clk) $fell(cs_n) |-> eight_bits_transfer;
  endproperty

  a_complete_byte: assert property(p_complete_byte) 
    else `uvm_error("MON_ASSERT", "Incomplete byte transfer");
  c_complete_byte: cover property(p_complete_byte);

endmodule : spi_monitor_assertions
