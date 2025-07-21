`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_agent extends uvm_agent;
  `uvm_component_utils(async_fifo_agent)

  async_fifo_driver driver;
  async_fifo_monitor monitor;
  async_fifo_sequencer sequencer;
  
  uvm_analysis_port #(async_fifo_transaction) ap;

  function new(string name = "async_fifo_agent", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    monitor = async_fifo_monitor::type_id::create("monitor", this);
    
    if (get_is_active() == UVM_ACTIVE) begin
      driver = async_fifo_driver::type_id::create("driver", this);
      sequencer = async_fifo_sequencer::type_id::create("sequencer", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    if (get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
    
    // Connect monitor's analysis port to agent's analysis port
    monitor.ap.connect(ap);
  endfunction

endclass 