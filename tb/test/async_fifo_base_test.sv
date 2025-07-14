`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_base_test extends uvm_test;
  `uvm_component_utils(async_fifo_base_test)

  async_fifo_env env;
  async_fifo_config cfg;

  function new(string name = "async_fifo_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create and configure the environment
    env = async_fifo_env::type_id::create("env", this);
    
    // Create and configure the configuration object
    cfg = async_fifo_config::type_id::create("cfg");
    cfg.DATA_WIDTH = 32;
    cfg.ADDRESS_WIDTH = 5;
    cfg.SYNC_STAGE = 2;
    cfg.RESET_MEM = 1;
    cfg.SOFT_RESET = 3;
    cfg.POWER_SAVE = 1;
    cfg.STICKY_ERROR = 0;
    cfg.PIPE_WRITE = 0;
    cfg.PIPE_READ = 0;
    cfg.DEBUG_ENABLE = 1;
    cfg.wclk_period = 10.0; // 100MHz
    cfg.rclk_period = 15.0; // 66.67MHz
    
    // Set configuration in config database
    uvm_config_db#(async_fifo_config)::set(this, "*", "cfg", cfg);
  endfunction

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_top.print_topology();
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    // Set timeout
    phase.raise_objection(this);
    #1000000; // 1ms timeout
    phase.drop_objection(this);
  endtask

endclass 