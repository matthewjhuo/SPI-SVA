// SPI Protocol Assertions
module spi_assertions
  import uvm_pkg::*;
(
  input  logic        clk,    // System Clock
  input  logic        rst_n,  // Active Low Reset
  input  logic        sclk,   // SPI Clock
  input  logic        cs_n,   // Chip Select (Active Low)
  input  logic        mosi,   // Master Out Slave In
  input  logic        miso    // Master In Slave Out
);

  // Clock & Reset Properties
  property p_reset_active;
    @(posedge clk) $rose(rst_n) |=> !cs_n;
  endproperty

  // CS Timing Properties
  property p_cs_setup;
    @(posedge clk) $fell(cs_n) |-> ##[0:2] $fell(sclk);
  endproperty

  property p_cs_hold;
    @(posedge clk) $rose(cs_n) |-> ##[0:2] !$changed(sclk);
  endproperty

  // SCLK Timing Properties  
  property p_sclk_period;
    @(posedge clk) $rose(sclk) |-> ##[1:4] $fell(sclk);
  endproperty

  property p_sclk_inactive;
    @(posedge clk) cs_n |-> !$changed(sclk);
  endproperty

  // Data Transfer Properties
  property p_mosi_stable;
    @(posedge sclk) $stable(mosi);
  endproperty

  property p_miso_stable; 
    @(posedge sclk) $stable(miso);
  endproperty

  property p_data_valid;
    @(posedge sclk) !cs_n |-> (!$isunknown(mosi) && !$isunknown(miso));
  endproperty

  // Assert all properties
  a_reset_active:  assert property(p_reset_active)  else `uvm_error("SPI_ASSERT", "Reset did not activate properly");
  a_cs_setup:      assert property(p_cs_setup)      else `uvm_error("SPI_ASSERT", "CS setup time violation");
  a_cs_hold:       assert property(p_cs_hold)       else `uvm_error("SPI_ASSERT", "CS hold time violation");
  a_sclk_period:   assert property(p_sclk_period)   else `uvm_error("SPI_ASSERT", "SCLK period violation");
  a_sclk_inactive: assert property(p_sclk_inactive) else `uvm_error("SPI_ASSERT", "SCLK active when CS inactive");
  a_mosi_stable:   assert property(p_mosi_stable)   else `uvm_error("SPI_ASSERT", "MOSI not stable at SCLK posedge");
  a_miso_stable:   assert property(p_miso_stable)   else `uvm_error("SPI_ASSERT", "MISO not stable at SCLK posedge");
  a_data_valid:    assert property(p_data_valid)    else `uvm_error("SPI_ASSERT", "Invalid data during transfer");

  // Cover properties
  c_reset_active:  cover property(p_reset_active);
  c_cs_setup:      cover property(p_cs_setup);
  c_cs_hold:       cover property(p_cs_hold);
  c_sclk_period:   cover property(p_sclk_period);
  c_sclk_inactive: cover property(p_sclk_inactive);
  c_mosi_stable:   cover property(p_mosi_stable);
  c_miso_stable:   cover property(p_miso_stable);
  c_data_valid:    cover property(p_data_valid);

endmodule : spi_assertions
