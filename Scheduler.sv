//This file contains the Scheduler which handles out of order execution 
//as well as Open Page Policy.
//Author: Sriram VB

module Scheduler
#(
`include "Definitions.pkg",
	parameter threshold = 5
)
(
	input logic [DATAWIDTH-1:0] DataIn,
	input logic [ADDRESSWIDTH-1:0] AddrIn,
	input logic rw_in,reset,clock,
	input logic done,valid,buff,
	input [BuffBits-1:0] tagfsm,
	output logic [DATAWIDTH-1:0] DataOut,
	output logic [ADDRESSWIDTH-1:0] AddrOut,
	output logic rw_out, full,refresh,ap, 
	output logic start,
	output logic [BuffBits -1:0]tagread, tag,
	output logic PageMiss, PageEmpty,
	output logic [1:0] PageHit
);

////////////////////////QUEUE/////////////////////////////////
typedef struct packed 
{
	bit rw;
	logic [DATAWIDTH-1:0] data;
	//logic [ADDRESSWIDTH-1:0] address;
	logic [RWIDTH-1:0] row;
	logic [CWIDTH-1:0] column;
	logic [BWIDTH-1:0] bank;
	logic [BGWIDTH-1:0] bankgrp;
	logic  rstcount; 
}Transaction;
Transaction CurrentTx;
Transaction Queue[BuffLength];

assign refresh = 1'b0;
assign ap = 1'b0;

///////////////////////////////////////
wire checkthresh;
wire empty;
logic NextPageHitL, NextPageHitS;
logic [BuffBits-1:0] PageHitIndL,PageHitIndS;

typedef logic [15:0] Count;
Count [BuffLength - 1:0]Counters;

logic [BuffBits-1:0] Readptr,Writeptr;
logic [BuffBits-1:0] NextTr;

logic [BuffLength-1:0] Freelist;
logic [BuffLength-1:0] ThresholdCrossed;

logic [BuffLength-1:0] ScheduledList;

logic [BuffBits-1:0] MaxValue;

logic [2:0] PageHitT;
logic PageMissT;
logic PageEmptyT;

typedef struct packed
{
	bit valid;
	logic [RWIDTH - 1:0] RowAddress;
}OpenRow;
OpenRow [BANKGROUP*BANKS -1:0]OpenRowList;

///////////////////Outputs to the CPU side modules////////////////
assign full = &Freelist; // bitwise AND of all the bits in the Freelist array
assign empty = ~(|Freelist);
assign tag = valid?Writeptr:'z;

///////////////Logic for filling the Queue///////////////////////////////
// write pointer pointing to the first empty memory
always_latch begin
	if(!full) begin
		unique case(Freelist) inside
			8'bxxxx_xxx0: Writeptr = 3'd0;
			8'bxxxx_xx01: Writeptr = 3'd1;
			8'bxxxx_x011: Writeptr = 3'd2;
			8'bxxxx_0111: Writeptr = 3'd3;
			8'bxxx0_1111: Writeptr = 3'd4;
			8'bxx01_1111: Writeptr = 3'd5;
			8'bx011_1111: Writeptr = 3'd6;
			8'b0111_1111: Writeptr = 3'd7;
		endcase
	end
end

// writing into the queue 
always_ff@(posedge clock) begin
	if(valid) begin
		Queue[Writeptr].rw <= rw_in;
		Queue[Writeptr].row <= AddrIn[31:17];
		Queue[Writeptr].column <= {AddrIn[14:8],AddrIn[5:3]};
		Queue[Writeptr].bank <= AddrIn[16:15];
		Queue[Writeptr].bankgrp <= AddrIn[7:6];
		Queue[Writeptr].data <= DataIn;
		Queue[Writeptr].rstcount <= 1'b1;
		$display($time,"\tWriteptr: %0d\tQueue[ptr]=%x",Writeptr, AddrIn);
	end
	else begin
		for(int i=0;i<BuffLength;i++)
			Queue[i].rstcount <= 1'b0;
	end
end

// maintaining the counter
always_ff@(posedge clock) begin
	integer i;
	for (i = 0; i < BuffLength; i++) begin
		if(Queue[i].rstcount || ~Freelist[i] || ScheduledList[i])
			Counters[i] <= '0;
		else begin	//only if data is present in the location
			Counters[i] <= Counters[i] + 1'b1;
	end
	end
end

// Freelist
always_ff@(posedge clock) begin
	if(reset) 
		Freelist <= '0;
	else begin
	if(valid)
		Freelist[Writeptr] <= 1'b1;
	if(start && !rw_out)
		Freelist[tagread] <= 1'b0; 
	if(buff)
		Freelist[tagfsm] <= 1'b0;
	end
end

always_ff@(posedge clock) begin
	if(reset)
		ScheduledList <= '0;
	else begin
		if(start && rw_out)
			ScheduledList[tagread] <= 1'b1;
		if(buff)
			ScheduledList[tagfsm] <= 1'b0;
	end
end

/////////////////////Scheduling Logic////////////////////////////////////
// Inorder execution with open page policy
// FSM states: see the rows accessed in the queue along with the counter
// values and pass these to a function which will return back the next state
// to be executed. wait now for the signal done and on receiving the signal
// done, give it to the fsm and prepare for the next.
// stores the maximum value of counter's index in MaxValue

CalcMax #(.BuffLength(BuffLength)) CM (Counters, MaxValue);

// Checks if any of the Counters crosses the threshold and sets that bit
always_comb begin
	integer i;
	for (i = 0; i<BuffLength; i++) begin
		if(Counters[i] > Threshold)
			ThresholdCrossed[i] = 1'b1;
		else
			ThresholdCrossed[i] = 1'b0;
	end
end

assign checkthresh = |ThresholdCrossed;

function automatic bit OpenPageShort(input logic [BuffBits-1:0] i);
	bit Open;
	if(Queue[i].row == OpenRowList[{Queue[i].bankgrp, Queue[i].bank}].RowAddress && OpenRowList[{Queue[i].bankgrp, Queue[i].bank}].valid && Freelist[i] && CurrentTx.bankgrp!=Queue[i].bankgrp && !ScheduledList[i])
		Open = 1'b1;
	else
		Open = 1'b0;
	return Open;
endfunction

function automatic bit OpenPageLong(input logic [BuffBits-1:0] i);
	bit Open;
	if(Queue[i].row == OpenRowList[{Queue[i].bankgrp, Queue[i].bank}].RowAddress && OpenRowList[{Queue[i].bankgrp, Queue[i].bank}].valid && Freelist[i] && !ScheduledList[i])
		Open = 1'b1;
	else
		Open = 1'b0;
	return Open;
endfunction


always_comb begin
	NextPageHitS = 1'b0;
	case(1'b1)
	OpenPageShort(3'd0): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd0;
					end
	OpenPageShort(3'd1): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd1;
					end
	OpenPageShort(3'd2): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd2;
					end
	OpenPageShort(3'd3): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd3;
					end
	OpenPageShort(3'd4): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd4;
					end
	OpenPageShort(3'd5): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd5;
					end
	OpenPageShort(3'd6): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd6;
					end
	OpenPageShort(3'd7): begin 
						NextPageHitS = 1'b1;
						PageHitIndS = 3'd7;
					end
	endcase

	
end

always_comb begin
	NextPageHitL = 1'b0;
	case(1'b1)
	OpenPageLong(3'd0): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd0;
					end
	OpenPageLong(3'd1): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd1;
					end
	OpenPageLong(3'd2): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd2;
					end
	OpenPageLong(3'd3): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd3;
					end
	OpenPageLong(3'd4): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd4;
					end
	OpenPageLong(3'd5): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd5;
					end
	OpenPageLong(3'd6): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd6;
					end
	OpenPageLong(3'd7): begin 
						NextPageHitL = 1'b1;
						PageHitIndL = 3'd7;
					end
	endcase
end

// Next State logic 
always_comb begin
	// Checking threshold
	if(checkthresh) begin
		NextTr = MaxValue;
		if(OpenPageShort(MaxValue))
			{PageHitT,PageMissT,PageEmptyT} = 4'b1000;
		else if(OpenPageLong(MaxValue))
			{PageHitT,PageMissT,PageEmptyT} = 4'b1100;
		else if(OpenRowList[{Queue[MaxValue].bankgrp,Queue[MaxValue].bank}].valid)
			{PageHitT,PageMissT,PageEmptyT} = 4'b0010;
		else
			{PageHitT,PageMissT,PageEmptyT} = 4'b0001;
	end
	
	// checking for tccds
	else if(NextPageHitS) begin
		NextTr = PageHitIndS;
		{PageHitT,PageMissT,PageEmptyT} = 4'b1000;
	end
	
	// checking for tccdl
	else if(NextPageHitL) begin
		NextTr = PageHitIndL;
		{PageHitT,PageMissT,PageEmptyT} = 4'b1100;
	end
	
	// checking for the max value
	else begin 
		NextTr = MaxValue;
		if(OpenRowList[{Queue[MaxValue].bankgrp,Queue[MaxValue].bank}].valid)
			{PageHitT,PageMissT,PageEmptyT} = 4'b0010;
		else
			{PageHitT,PageMissT,PageEmptyT} = 4'b0001;
	end
end

// Giving values when done comes
always_ff@(posedge clock) begin
	if(start || empty || !done)
		start <= 1'b0;
	else
		start <= 1'b1;
end

always_ff@(posedge clock) begin
	if(done) begin
		CurrentTx <= Queue[NextTr];
		{PageHit,PageMiss,PageEmpty} <= {PageHitT,PageMissT,PageEmptyT};
		Readptr <= NextTr;
		tagread <= NextTr;
	end
end

// writing into the queue 
always_ff@(posedge clock) begin
	if(done) begin
		rw_out <= Queue[NextTr].rw;
	 	AddrOut[31:17] <= Queue[NextTr].row;
		AddrOut[14:8] <= Queue[NextTr].column[CWIDTH-1:3];
		AddrOut[16:15] <= Queue[NextTr].bank;
		AddrOut[7:6] <= Queue[NextTr].bankgrp;
		AddrOut[5:0] <= 6'b0;
		DataOut <= Queue[NextTr].data;
	end
end

// updating the table of open rows
always_ff@(posedge clock) begin
	int i;
	if(reset) begin
		for(i=0;i<BuffLength;i++)
			OpenRowList[i].valid = 1'b0;
	end
	else if(start)
		OpenRowList[{CurrentTx.bankgrp,CurrentTx.bank}].valid = 1'b1;
		OpenRowList[{CurrentTx.bankgrp,CurrentTx.bank}].RowAddress = CurrentTx.row;
end

endmodule
