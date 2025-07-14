`timescale 1ns/1ps

interface async_fifo_if(input logic wclk, rclk, hw_rst);
  
  // Write side signals
  logic [31:0] wdata;
  logic write_enable;
  logic [4:0] afull_value;
  
  // Read side signals
  logic [31:0] read_data;
  logic read_enable;
  logic [4:0] aempty_value;
  
  // Control signals
  logic sw_rst;
  logic mem_rst;
  
  // Status signals
  logic wfull;
  logic rdempty;
  logic wr_almost_ful;
  logic rd_almost_empty;
  logic overflow;
  logic underflow;
  logic [5:0] fifo_write_count;
  logic [5:0] fifo_read_count;
  logic [5:0] wr_level;
  logic [5:0] rd_level;

  // Clocking blocks for write and read domains
  clocking write_cb @(posedge wclk);
    output wdata, write_enable, afull_value, sw_rst, mem_rst;
    input wfull, wr_almost_ful, overflow, fifo_write_count, wr_level;
  endclocking

  clocking read_cb @(posedge rclk);
    output read_enable, aempty_value;
    input read_data, rdempty, rd_almost_empty, underflow, fifo_read_count, rd_level;
  endclocking

  // Modport for write interface
  modport write_mp(clocking write_cb, input hw_rst);
  
  // Modport for read interface
  modport read_mp(clocking read_cb, input hw_rst);
  
  // Modport for monitor
  modport monitor_mp(input wclk, rclk, hw_rst, wdata, write_enable, afull_value, 
                     read_data, read_enable, aempty_value, sw_rst, mem_rst,
                     wfull, rdempty, wr_almost_ful, rd_almost_empty, overflow, 
                     underflow, fifo_write_count, fifo_read_count, wr_level, rd_level);

  // Default clocking for convenience
  default clocking default_cb @(posedge wclk);

  // Tasks for common operations
  task automatic write_data(input logic [31:0] data, input logic [4:0] afull_val = 5'd20);
    write_cb.wdata <= data;
    write_cb.afull_value <= afull_val;
    write_cb.write_enable <= 1'b1;
    @(write_cb);
    write_cb.write_enable <= 1'b0;
  endtask

  task automatic read_data(output logic [31:0] data, input logic [4:0] aempty_val = 5'd5);
    read_cb.aempty_value <= aempty_val;
    read_cb.read_enable <= 1'b1;
    @(read_cb);
    data = read_cb.read_data;
    read_cb.read_enable <= 1'b0;
  endtask

  task automatic reset_fifo();
    sw_rst = 1'b1;
    mem_rst = 1'b1;
    @(posedge wclk);
    @(posedge rclk);
    sw_rst = 1'b0;
    mem_rst = 1'b0;
  endtask

  // Properties for assertions
  property no_write_when_full;
    @(posedge wclk) disable iff (!hw_rst)
      wfull |-> !write_enable;
  endproperty

  property no_read_when_empty;
    @(posedge rclk) disable iff (!hw_rst)
      rdempty |-> !read_enable;
  endproperty

  property overflow_implies_full;
    @(posedge wclk) disable iff (!hw_rst)
      overflow |-> wfull;
  endproperty

  property underflow_implies_empty;
    @(posedge rclk) disable iff (!hw_rst)
      underflow |-> rdempty;
  endproperty

  // Assertions
  assert property (no_write_when_full)
    else $error("Write attempted when FIFO is full");
    
  assert property (no_read_when_empty)
    else $error("Read attempted when FIFO is empty");
    
  assert property (overflow_implies_full)
    else $error("Overflow occurred when FIFO is not full");
    
  assert property (underflow_implies_empty)
    else $error("Underflow occurred when FIFO is not empty");

endinterface 