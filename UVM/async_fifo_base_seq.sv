`timescale 1ns/1ps

`include "async_fifo_config.sv"
`include "async_fifo_transaction.sv"

class async_fifo_base_seq extends uvm_sequence #(async_fifo_transaction);
  `uvm_object_utils(async_fifo_base_seq)

  async_fifo_config cfg;
  int num_transactions = 100;

  function new(string name = "async_fifo_base_seq");
    super.new(name);
  endfunction

  task pre_body();
    if (!uvm_config_db#(async_fifo_config)::get(null, get_full_name(), "cfg", cfg))
      `uvm_fatal("NOCFG", "Configuration not found")
  endtask

  task body();
    `uvm_info(get_type_name(), "Starting base sequence", UVM_LOW)
    
    repeat (num_transactions) begin
      `uvm_do(req)
    end
    
    `uvm_info(get_type_name(), "Base sequence completed", UVM_LOW)
  endtask

endclass 