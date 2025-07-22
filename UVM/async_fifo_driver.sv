`timescale 1ns/1ps

`include "async_fifo_config.sv"
`include "async_fifo_transaction.sv"

class async_fifo_driver extends uvm_driver #(async_fifo_transaction);
  `uvm_component_utils(async_fifo_driver)

  virtual async_fifo_if.write_mp vif;
  async_fifo_config cfg;

  function new(string name = "async_fifo_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual async_fifo_if.write_mp)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
      
    if (!uvm_config_db#(async_fifo_config)::get(this, "", "cfg", cfg))
      `uvm_fatal("NOCFG", "Configuration not found")
  endfunction

  task run_phase(uvm_phase phase);
    async_fifo_transaction tr;
    
    // Initialize interface
    vif.write_cb.wdata <= '0;
    vif.write_cb.write_enable <= 1'b0;
    vif.write_cb.afull_value <= '0;
    vif.write_cb.sw_rst <= 1'b0;
    vif.write_cb.mem_rst <= 1'b0;
    
    forever begin
      seq_item_port.get_next_item(tr);
      drive_transaction(tr);
      seq_item_port.item_done();
    end
  endtask

  task drive_transaction(async_fifo_transaction tr);
    `uvm_info(get_type_name(), $sformatf("Driving transaction: %s", tr.convert2string()), UVM_HIGH)
    
    // Drive write signals
    vif.write_cb.wdata <= tr.wdata;
    vif.write_cb.write_enable <= tr.write_enable;
    vif.write_cb.afull_value <= tr.afull_value;
    vif.write_cb.sw_rst <= tr.sw_rst;
    vif.write_cb.mem_rst <= tr.mem_rst;
    
    // Wait for clock edge
    @(vif.write_cb);
    
    // Sample response signals
    tr.wfull = vif.write_cb.wfull;
    tr.wr_almost_ful = vif.write_cb.wr_almost_ful;
    tr.overflow = vif.write_cb.overflow;
    tr.fifo_write_count = vif.write_cb.fifo_write_count;
    tr.wr_level = vif.write_cb.wr_level;
    
    // Clear write enable after one cycle
    vif.write_cb.write_enable <= 1'b0;
    
    `uvm_info(get_type_name(), $sformatf("Transaction completed: wfull=%b, overflow=%b", 
              tr.wfull, tr.overflow), UVM_HIGH)
  endtask

endclass 