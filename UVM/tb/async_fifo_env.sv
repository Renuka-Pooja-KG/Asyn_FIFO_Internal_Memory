`timescale 1ns/1ps

import async_fifo_pkg::*;

class async_fifo_env extends uvm_env;
  `uvm_component_utils(async_fifo_env)

  async_fifo_agent agent;
  async_fifo_scoreboard scoreboard;
  async_fifo_coverage coverage;

  function new(string name = "async_fifo_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    agent = async_fifo_agent::type_id::create("agent", this);
    scoreboard = async_fifo_scoreboard::type_id::create("scoreboard", this);
    coverage = async_fifo_coverage::type_id::create("coverage", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect agent's analysis port to scoreboard and coverage
    agent.ap.connect(scoreboard.write_export);
    agent.ap.connect(scoreboard.read_export);
    agent.ap.connect(coverage.analysis_export);
  endfunction

endclass 