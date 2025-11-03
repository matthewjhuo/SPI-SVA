// SPI Master Assertions
module spi_master_assertions (
    input  logic        clk,          // System Clock
    input  logic        rst_n,        // Active Low Reset
    input  logic        sclk,         // SPI Clock
    input  logic        cs_n,         // Chip Select (Active Low)
    input  logic        mosi,         // Master Out Slave In
    input  logic [7:0]  tx_data,      // Data to transmit
    input  logic        tx_valid,     // Transmit data valid
    input  logic        tx_ready      // Ready to accept new data
);

  // Master Clock Generation Properties
  property p_sclk_generation;
    @(posedge clk) tx_valid && tx_ready |-> ##[1:2] !$stable(sclk);
  endproperty

  // Master CS Control Properties
  property p_cs_control;
    @(posedge clk) tx_valid |-> ##[0:2] !cs_n;
  endproperty

  property p_cs_deassert;
    @(posedge clk) !tx_valid && !tx_ready |-> ##[1:4] cs_n;
  endproperty

  // Master Data Output Properties
  property p_mosi_change;
    @(negedge sclk) !cs_n |-> ##1 $stable(mosi);
  endproperty

  property p_tx_data_valid;
    @(posedge clk) (tx_valid && tx_ready) |-> !$isunknown(tx_data);
  endproperty

  // Master Transfer Control Properties
  property p_transfer_complete;
    @(posedge clk) $fell(cs_n) |-> ##[8:16] $rose(cs_n);
  endproperty

  property p_no_overlap_transfer;
    @(posedge clk) $rose(cs_n) |-> ##[1:$] $fell(cs_n);
  endproperty

  // Assert all properties
  a_sclk_generation:    assert property(p_sclk_generation)    
    else `uvm_error("MASTER_ASSERT", "SCLK generation failed");
  a_cs_control:         assert property(p_cs_control)         
    else `uvm_error("MASTER_ASSERT", "CS control violation");
  a_cs_deassert:       assert property(p_cs_deassert)        
    else `uvm_error("MASTER_ASSERT", "CS deassert violation");
  a_mosi_change:       assert property(p_mosi_change)        
    else `uvm_error("MASTER_ASSERT", "MOSI change at wrong time");
  a_tx_data_valid:     assert property(p_tx_data_valid)      
    else `uvm_error("MASTER_ASSERT", "Invalid TX data");
  a_transfer_complete: assert property(p_transfer_complete)  
    else `uvm_error("MASTER_ASSERT", "Transfer did not complete");
  a_no_overlap:        assert property(p_no_overlap_transfer) 
    else `uvm_error("MASTER_ASSERT", "Transfers overlapped");

  // Cover properties
  c_sclk_generation:    cover property(p_sclk_generation);
  c_cs_control:         cover property(p_cs_control);
  c_cs_deassert:       cover property(p_cs_deassert);
  c_mosi_change:       cover property(p_mosi_change);
  c_tx_data_valid:     cover property(p_tx_data_valid);
  c_transfer_complete: cover property(p_transfer_complete);
  c_no_overlap:        cover property(p_no_overlap_transfer);

endmodule : spi_master_assertions
