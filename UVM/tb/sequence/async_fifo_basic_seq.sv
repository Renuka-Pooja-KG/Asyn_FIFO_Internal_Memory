`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_basic_seq #(parameter DATA_WIDTH = 32, parameter ADDRESS_WIDTH = 5) extends async_fifo_base_seq #(DATA_WIDTH, ADDRESS_WIDTH);
  `uvm_object_utils(async_fifo_basic_seq)

  function new(string name = "async_fifo_basic_seq");
    super.new(name);
    num_transactions = 50;
  endfunction

  task body();
    `uvm_info(get_type_name(), "Starting basic FIFO functionality test", UVM_LOW)
    
    // Test 1: Write until full
    `uvm_info(get_type_name(), "Test 1: Write until full", UVM_MEDIUM)
    repeat (32) begin // FIFO depth is 32
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(25);
        req.aempty_value == 'unsigned'(5);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 2: Read until empty
    `uvm_info(get_type_name(), "Test 2: Read until empty", UVM_MEDIUM)
    repeat (32) begin
      `uvm_do_with(req, {
        req.write_enable == 0;
        req.read_enable == 1;
        req.afull_value == 'unsigned'(25);
        req.aempty_value == 'unsigned'(5);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 3: Write and read simultaneously
    `uvm_info(get_type_name(), "Test 3: Write and read simultaneously", UVM_MEDIUM)
    repeat (20) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 1;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(25);
        req.aempty_value == 'unsigned'(5);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 4: Almost full/empty conditions
    `uvm_info(get_type_name(), "Test 4: Almost full/empty conditions", UVM_MEDIUM)
    repeat (15) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(15);
        req.aempty_value == 'unsigned'(5);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    repeat (15) begin
      `uvm_do_with(req, {
        req.write_enable == 0;
        req.read_enable == 1;
        req.afull_value == 'unsigned'(25);
        req.aempty_value == 'unsigned'(15);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 5: Simultaneous write and read (corner case)
    `uvm_info(get_type_name(), "Test 5: Simultaneous write and read (corner case)", UVM_MEDIUM)
    repeat (10) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 1;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(20);
        req.aempty_value == 'unsigned'(10);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    `uvm_info(get_type_name(), "Basic FIFO functionality test completed", UVM_LOW)
  endtask

endclass 