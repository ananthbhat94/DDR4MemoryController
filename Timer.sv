//This module implements a synthezizable timer
//It is used in the Controller_FSM file.
//This module is written by our Prof. Mark Faust
//Author: Mark Faust

module CountdownTimer(clock, Reset, HitZero,Load);
input clock;
input Reset;
input logic [31:0] Load;
output HitZero;

reg [31:0] Count;

assign HitZero = (Count == 0);

always @(posedge clock)
begin
if (Reset)
    Count <= Load;
else
    Count <= Count - 1;
end
endmodule


