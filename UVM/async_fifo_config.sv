`timescale 1ns/1ps

import uvm_pkg::*;
`include "uvm_macros.svh"

class async_fifo_config extends uvm_object;
  `uvm_object_utils(async_fifo_config)

  // FIFO parameters
  int DATA_WIDTH = 32;
  int ADDRESS_WIDTH = 5;
  int SYNC_STAGE = 2;
  int RESET_MEM = 1;
  int SOFT_RESET = 3;
  int POWER_SAVE = 1;
  int STICKY_ERROR = 0;
  int PIPE_WRITE = 0;
  int PIPE_READ = 0;
  int DEBUG_ENABLE = 1;

  // Clock parameters
  real wclk_period = 10.0; // 100MHz
  real rclk_period = 15.0; // 66.67MHz

  function new(string name = "async_fifo_config");
    super.new(name);
  endfunction

endclass 