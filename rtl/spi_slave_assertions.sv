// SPI Slave Assertions
module spi_slave_assertions
  import uvm_pkg::*;
(
  input  logic        clk,          // System Clock
  input  logic        rst_n,        // Active Low Reset
  input  logic        sclk,         // SPI Clock
  input  logic        cs_n,         // Chip Select (Active Low)
  input  logic        miso,         // Master In Slave Out
  input  logic [7:0]  rx_data,      // Received data
  input  logic        rx_valid,     // Received data valid
  input  logic [7:0]  tx_data,      // Data to transmit
  input  logic        tx_ready      // Ready to accept new data
);

  // Slave Clock Synchronization Properties
  property p_sclk_sync;
    @(posedge clk) $rose(sclk) |-> ##[0:1] rx_valid;
  endproperty

  // Slave CS Response Properties
  property p_cs_response;
    @(posedge clk) !cs_n |-> ##[1:2] tx_ready;
  endproperty

  // Slave Data Output Properties
  property p_miso_change;
    @(negedge sclk) !cs_n |-> ##1 $stable(miso);
  endproperty

  property p_rx_data_valid;
    @(posedge clk) rx_valid |-> !$isunknown(rx_data);
  endproperty

  // Slave Transfer Properties
  property p_data_capture;
    @(posedge sclk) !cs_n |=> ##7 rx_valid;
  endproperty

  property p_slave_ready;
    @(posedge clk) $fell(cs_n) |-> ##[0:2] tx_ready;
  endproperty

  property p_no_tx_when_inactive;
    @(posedge clk) cs_n |-> !tx_ready;
  endproperty

  // Assert all properties
  a_sclk_sync:          assert property(p_sclk_sync)          
    else `uvm_error("SLAVE_ASSERT", "SCLK synchronization failed");
  a_cs_response:        assert property(p_cs_response)        
    else `uvm_error("SLAVE_ASSERT", "CS response violation");
  a_miso_change:        assert property(p_miso_change)        
    else `uvm_error("SLAVE_ASSERT", "MISO change at wrong time");
  a_rx_data_valid:      assert property(p_rx_data_valid)      
    else `uvm_error("SLAVE_ASSERT", "Invalid RX data");
  a_data_capture:       assert property(p_data_capture)       
    else `uvm_error("SLAVE_ASSERT", "Data capture failed");
  a_slave_ready:        assert property(p_slave_ready)        
    else `uvm_error("SLAVE_ASSERT", "Slave not ready after CS");
  a_no_tx_when_inactive: assert property(p_no_tx_when_inactive) 
    else `uvm_error("SLAVE_ASSERT", "Transmitting when inactive");

  // Cover properties
  c_sclk_sync:          cover property(p_sclk_sync);
  c_cs_response:        cover property(p_cs_response);
  c_miso_change:        cover property(p_miso_change);
  c_rx_data_valid:      cover property(p_rx_data_valid);
  c_data_capture:       cover property(p_data_capture);
  c_slave_ready:        cover property(p_slave_ready);
  c_no_tx_when_inactive: cover property(p_no_tx_when_inactive);

endmodule : spi_slave_assertions
