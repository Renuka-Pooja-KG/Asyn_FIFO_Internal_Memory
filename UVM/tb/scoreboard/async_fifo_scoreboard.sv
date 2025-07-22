`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(async_fifo_scoreboard)

  async_fifo_config cfg;
  uvm_analysis_export #(async_fifo_transaction) write_export;
  uvm_analysis_export #(async_fifo_transaction) read_export;
  
  uvm_tlm_analysis_fifo #(async_fifo_transaction) write_fifo;
  uvm_tlm_analysis_fifo #(async_fifo_transaction) read_fifo;
  
  // Data integrity checking
  logic [31:0] expected_data_queue[$];
  int write_count = 0;
  int read_count = 0;
  int error_count = 0;
  
  // FIFO state tracking
  int expected_wr_level = 0;
  int expected_rd_level = 0;
  logic expected_wfull = 0;
  logic expected_rdempty = 1;

  function new(string name = "async_fifo_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    write_export = new("write_export", this);
    read_export = new("read_export", this);
    write_fifo = new("write_fifo", this);
    read_fifo = new("read_fifo", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(async_fifo_config)::get(this, "", "cfg", cfg))
      `uvm_fatal("NOCFG", "Configuration not found")
    expected_wr_level = 0;
    expected_rd_level = (1 << cfg.ADDRESS_WIDTH); // FIFO depth
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    write_export.connect(write_fifo.analysis_export);
    read_export.connect(read_fifo.analysis_export);
  endfunction

  task run_phase(uvm_phase phase);
    fork
      check_write_transactions();
      check_read_transactions();
      check_fifo_behavior();
    join
  endtask

  task check_write_transactions();
    async_fifo_transaction tr;
    
    forever begin
      write_fifo.get(tr);
      // Simultaneous write and read: do not update levels or queue
      if (tr.write_enable && tr.read_enable && !tr.wfull && !tr.rdempty) begin
        `uvm_info(get_type_name(), "Simultaneous write and read: levels unchanged", UVM_MEDIUM)
        // No change to expected_wr_level or expected_rd_level
        // No update to expected_data_queue
      end else begin
        if (tr.write_enable && !tr.wfull) begin
          // Store expected data
          expected_data_queue.push_back(tr.wdata);
          write_count++;
          // Update expected FIFO state
          if (expected_wr_level < (1 << cfg.ADDRESS_WIDTH)) begin
            expected_wr_level++;
            expected_rd_level--;
          end
          expected_wfull = (expected_wr_level == (1 << cfg.ADDRESS_WIDTH));
          expected_rdempty = (expected_wr_level == 0);
          `uvm_info(get_type_name(), $sformatf("Write: data=0x%h, wr_level=%d, wfull=%b", 
                    tr.wdata, expected_wr_level, expected_wfull), UVM_HIGH)
        end
      end
      // Check for overflow
      if (tr.overflow && !expected_wfull) begin
        `uvm_error(get_type_name(), "Unexpected overflow detected")
        error_count++;
      end
      // Check FIFO state consistency
      if (tr.wfull != expected_wfull) begin
        `uvm_error(get_type_name(), $sformatf("FIFO full state mismatch: expected=%b, actual=%b", 
                  expected_wfull, tr.wfull))
        error_count++;
      end
    end
  endtask

  task check_read_transactions();
    async_fifo_transaction tr;
    logic [31:0] expected_data;
    
    forever begin
      read_fifo.get(tr);
      // Simultaneous write and read: do not update levels or queue
      if (tr.write_enable && tr.read_enable && !tr.wfull && !tr.rdempty) begin
        `uvm_info(get_type_name(), "Simultaneous write and read: levels unchanged (read)", UVM_MEDIUM)
        // No change to expected_wr_level or expected_rd_level
        // No update to expected_data_queue
      end else begin
        if (tr.read_enable && !tr.rdempty) begin
          // Check data integrity
          if (expected_data_queue.size() > 0) begin
            expected_data = expected_data_queue.pop_front();
            read_count++;
            if (tr.read_data !== expected_data) begin
              `uvm_error(get_type_name(), $sformatf("Data integrity error: expected=0x%h, actual=0x%h", 
                        expected_data, tr.read_data))
              error_count++;
            end else begin
              `uvm_info(get_type_name(), $sformatf("Read: data=0x%h (correct)", tr.read_data), UVM_HIGH)
            end
            // Update expected FIFO state
            if (expected_wr_level > 0) begin
              expected_wr_level--;
              expected_rd_level++;
            end
            expected_wfull = (expected_wr_level == (1 << cfg.ADDRESS_WIDTH));
            expected_rdempty = (expected_wr_level == 0);
          end else begin
            `uvm_error(get_type_name(), "Read attempted but no data available")
            error_count++;
          end
        end
      end
      // Check for underflow
      if (tr.underflow && !expected_rdempty) begin
        `uvm_error(get_type_name(), "Unexpected underflow detected")
        error_count++;
      end
      // Check FIFO state consistency
      if (tr.rdempty != expected_rdempty) begin
        `uvm_error(get_type_name(), $sformatf("FIFO empty state mismatch: expected=%b, actual=%b", 
                  expected_rdempty, tr.rdempty))
        error_count++;
      end
    end
  endtask

  task check_fifo_behavior();
    // Monitor for invalid FIFO states
    forever begin
      @(posedge $time);
      // Check for invalid state (both full and empty)
      if (expected_wfull && expected_rdempty) begin
        `uvm_error(get_type_name(), "Invalid FIFO state: both full and empty")
        error_count++;
      end
      // Check level consistency
      if (expected_wr_level + expected_rd_level != (1 << cfg.ADDRESS_WIDTH)) begin
        `uvm_error(get_type_name(), $sformatf("FIFO level inconsistency: wr_level=%d, rd_level=%d", 
                  expected_wr_level, expected_rd_level))
        error_count++;
      end
    end
  endtask

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    
    `uvm_info(get_type_name(), $sformatf("Scoreboard Report:"), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("  Write transactions: %d", write_count), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("  Read transactions: %d", read_count), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("  Errors detected: %d", error_count), UVM_LOW)
    `uvm_info(get_type_name(), $sformatf("  Remaining data in queue: %d", expected_data_queue.size()), UVM_LOW)
    
    if (error_count == 0) begin
      `uvm_info(get_type_name(), "Scoreboard: All checks passed!", UVM_LOW)
    end else begin
      `uvm_error(get_type_name(), $sformatf("Scoreboard: %d errors detected", error_count))
    end
  endfunction

endclass 