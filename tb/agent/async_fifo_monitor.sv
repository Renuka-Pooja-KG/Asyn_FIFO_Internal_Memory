`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_monitor extends uvm_monitor;
  `uvm_component_utils(async_fifo_monitor)

  virtual async_fifo_if.monitor_mp vif;
  async_fifo_config cfg;
  uvm_analysis_port #(async_fifo_transaction) ap;
  
  // Coverage and analysis
  async_fifo_transaction tr;
  logic [31:0] write_data_queue[$];
  int write_count = 0;
  int read_count = 0;

  function new(string name = "async_fifo_monitor", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual async_fifo_if.monitor_mp)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
      
    if (!uvm_config_db#(async_fifo_config)::get(this, "", "cfg", cfg))
      `uvm_fatal("NOCFG", "Configuration not found")
  endfunction

  task run_phase(uvm_phase phase);
    fork
      monitor_write_domain();
      monitor_read_domain();
      monitor_reset_events();
    join
  endtask

  task monitor_write_domain();
    forever begin
      @(posedge vif.wclk);
      
      if (vif.hw_rst) begin
        if (vif.write_enable && !vif.wfull) begin
          // Capture write transaction
          tr = async_fifo_transaction::type_id::create("write_tr");
          tr.wdata = vif.wdata;
          tr.write_enable = vif.write_enable;
          tr.afull_value = vif.afull_value;
          tr.wfull = vif.wfull;
          tr.wr_almost_ful = vif.wr_almost_ful;
          tr.overflow = vif.overflow;
          tr.fifo_write_count = vif.fifo_write_count;
          tr.wr_level = vif.wr_level;
          tr.sw_rst = vif.sw_rst;
          tr.mem_rst = vif.mem_rst;
          
          // Store write data for data integrity check
          write_data_queue.push_back(vif.wdata);
          write_count++;
          
          `uvm_info(get_type_name(), $sformatf("Write transaction: data=0x%h, wfull=%b, overflow=%b", 
                    vif.wdata, vif.wfull, vif.overflow), UVM_HIGH)
          
          ap.write(tr);
        end
        
        // Monitor overflow conditions
        if (vif.overflow) begin
          `uvm_warning(get_type_name(), "Overflow detected!")
        end
      end
    end
  endtask

  task monitor_read_domain();
    forever begin
      @(posedge vif.rclk);
      
      if (vif.hw_rst) begin
        if (vif.read_enable && !vif.rdempty) begin
          // Capture read transaction
          tr = async_fifo_transaction::type_id::create("read_tr");
          tr.read_data = vif.read_data;
          tr.read_enable = vif.read_enable;
          tr.aempty_value = vif.aempty_value;
          tr.rdempty = vif.rdempty;
          tr.rd_almost_empty = vif.rd_almost_empty;
          tr.underflow = vif.underflow;
          tr.fifo_read_count = vif.fifo_read_count;
          tr.rd_level = vif.rd_level;
          
          read_count++;
          
          `uvm_info(get_type_name(), $sformatf("Read transaction: data=0x%h, empty=%b, underflow=%b", 
                    vif.read_data, vif.rdempty, vif.underflow), UVM_HIGH)
          
          ap.write(tr);
        end
        
        // Monitor underflow conditions
        if (vif.underflow) begin
          `uvm_warning(get_type_name(), "Underflow detected!")
        end
      end
    end
  endtask

  task monitor_reset_events();
    forever begin
      @(negedge vif.hw_rst);
      `uvm_info(get_type_name(), "Hardware reset detected", UVM_MEDIUM)
      
      // Clear queues on reset
      write_data_queue.delete();
      write_count = 0;
      read_count = 0;
      
      @(posedge vif.hw_rst);
      `uvm_info(get_type_name(), "Hardware reset released", UVM_MEDIUM)
    end
  endtask

  // Function to check data integrity
  function bit check_data_integrity(logic [31:0] expected_data);
    if (write_data_queue.size() > 0) begin
      logic [31:0] stored_data = write_data_queue.pop_front();
      return (expected_data == stored_data);
    end
    return 0;
  endfunction

  // Function to get FIFO statistics
  function void get_fifo_stats(output int writes, output int reads);
    writes = write_count;
    reads = read_count;
  endfunction

endclass 