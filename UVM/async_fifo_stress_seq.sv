`timescale 1ns/1ps

`include "async_fifo_config.sv"
`include "async_fifo_transaction.sv"
`include "async_fifo_base_seq.sv" // <-- This is required!

class async_fifo_stress_seq extends async_fifo_base_seq;
  `uvm_object_utils(async_fifo_stress_seq)

  function new(string name = "async_fifo_stress_seq");
    super.new(name);
    num_transactions = 200;
  endfunction

  task body();
    `uvm_info(get_type_name(), "Starting stress test", UVM_LOW)
    
    // Test 1: Rapid write/read cycles
    `uvm_info(get_type_name(), "Test 1: Rapid write/read cycles", UVM_MEDIUM)
    repeat (50) begin
      `uvm_do_with(req, {
        req.write_enable dist {1:=80, 0:=20};
        req.read_enable dist {1:=80, 0:=20};
        req.wdata inside {[{cfg.DATA_WIDTH{1'b0}}+1:{cfg.DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(20);
        req.aempty_value == 'unsigned'(10);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 2: Back-to-back operations
    `uvm_info(get_type_name(), "Test 2: Back-to-back operations", UVM_MEDIUM)
    repeat (30) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{cfg.DATA_WIDTH{1'b0}}+1:{cfg.DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(25);
        req.aempty_value == 'unsigned'(5);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    repeat (30) begin
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
    
    // Test 3: Corner case data patterns
    `uvm_info(get_type_name(), "Test 3: Corner case data patterns", UVM_MEDIUM)
    repeat (20) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {32'h0000_0000, 32'hFFFF_FFFF, 32'hAAAA_AAAA, 32'h5555_5555};
        req.afull_value == 'unsigned'(20);
        req.aempty_value == 'unsigned'(10);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 4: High-frequency operations with different almost full/empty values
    `uvm_info(get_type_name(), "Test 4: High-frequency operations", UVM_MEDIUM)
    repeat (40) begin
      `uvm_do_with(req, {
        req.write_enable dist {1:=70, 0:=30};
        req.read_enable dist {1:=70, 0:=30};
        req.wdata inside {[{cfg.DATA_WIDTH{1'b0}}+1:{cfg.DATA_WIDTH{1'b1}}]};
        req.afull_value inside {[10:30]};
        req.aempty_value inside {[5:25]};
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    // Test 5: Boundary conditions
    `uvm_info(get_type_name(), "Test 5: Boundary conditions", UVM_MEDIUM)
    repeat (30) begin
      `uvm_do_with(req, {
        req.write_enable == 1;
        req.read_enable == 0;
        req.wdata inside {[{cfg.DATA_WIDTH{1'b0}}+1:{cfg.DATA_WIDTH{1'b1}}]};
        req.afull_value == 'unsigned'(31);
        req.aempty_value == 'unsigned'(1);
        req.sw_rst == 0;
        req.hw_rst_n == 1;
        req.mem_rst == 0;
      })
    end
    
    `uvm_info(get_type_name(), "Stress test completed", UVM_LOW)
  endtask

endclass 