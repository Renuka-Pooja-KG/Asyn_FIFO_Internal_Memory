`timescale 1ns/1ps

`include "async_fifo_config.sv"
`include "async_fifo_transaction.sv"

class async_fifo_reset_seq #(parameter DATA_WIDTH = 32, parameter ADDRESS_WIDTH = 5) extends async_fifo_base_seq #(DATA_WIDTH, ADDRESS_WIDTH);
  `uvm_object_utils(async_fifo_reset_seq)

  function new(string name = "async_fifo_reset_seq");
    super.new(name);
    num_transactions = 100;
  endfunction

  task body();
    `uvm_info(get_type_name(), "Starting reset test", UVM_LOW)
    
    // Test 1: Hardware reset during operations
    `uvm_info(get_type_name(), "Test 1: Hardware reset during operations", UVM_MEDIUM)
    repeat (10) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Trigger hardware reset
    repeat (5) begin
      `uvm_do_with(req, {
        req.write_enable == 0;
        req.read_enable == 0;
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 0;
        req.mem_rst == 0;
      })
    end
    
    // Resume operations after reset
    repeat (10) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 2: Soft reset during operations
    `uvm_info(get_type_name(), "Test 2: Soft reset during operations", UVM_MEDIUM)
    repeat (15) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Trigger soft reset
    repeat (3) begin
      `uvm_do_with(req, {
        req.write_enable == 0;
        req.read_enable == 0;
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 1;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Resume operations after soft reset
    repeat (15) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 3: Memory reset
    `uvm_info(get_type_name(), "Test 3: Memory reset", UVM_MEDIUM)
    repeat (20) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Trigger memory reset
    repeat (2) begin
      `uvm_do_with(req, {
        req.write_enable == 0;
        req.read_enable == 0;
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 1;
      })
    end
    
    // Resume operations after memory reset
    repeat (20) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 4: Combined reset scenarios
    `uvm_info(get_type_name(), "Test 4: Combined reset scenarios", UVM_MEDIUM)
    repeat (10) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{DATA_WIDTH{1'b0}}+1:{DATA_WIDTH{1'b1}}]};
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Combined reset
    repeat (3) begin
      `uvm_do_with(req, {
        req.write_enable == 0;
        req.read_enable == 0;
        req.afull_value == 5'd20;
        req.aempty_value == 5'd10;
        req.sw_rst == 1;
        req.hw_rst_n == 0;
        req.mem_rst == 1;
      })
    end
    
    `uvm_info(get_type_name(), "Reset test completed", UVM_LOW)
  endtask

endclass 