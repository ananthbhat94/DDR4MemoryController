//This file contains the DDR4 interface definitons between the Memory and 
//the controller. This interface defines pin signals and contains methods 
//which can be used by both the memory controller as well as the memory.
//Basic assertions included within the interface check for timing violations
//Author: 	Ananth Bhat
//			Sriram VB
interface DDR4Interface
#(
	`include "Definitions.pkg"
)
(
	input logic clock,reset
);

//Definitions and LocalParameters
`define RAS A[16]	//RAS Command Input
`define CAS A[15] 	//CAS Command Input
`define WE	A[14]	//WE Command Input
`define BC	A[12] 	//Burst Chop
`define AP 	A[10]  	// Auto Precharge
`define HIGH '1
localparam LOW = '0;
localparam TRI ='z;

/**************Define Interface Signals*********************/
//Address Inputs
logic [AWIDTH-1:0] A; //Transaction Level Model(TLM) variable
wire [AWIDTH-1:0] pin_A; 

//Control Signals
logic act_n; //Activate Command Input
logic [BG_BITS-1:0] bg; //Bank Address Inputs
logic [B_BITS-1:0] b; //Bank Group Address Inputs
logic clk_t, clk_c; //Differential Clock Inputs
logic cke; //Clock Enable
logic cs_n; //Chip Select
logic dm_n,udm_n,ldm_n; //Input Data Mask
logic odt; //On Die Termination
logic par; //Parity
logic reset_n; //Asynchronous Reset
logic ten; //Connectivity Test Mode
logic alert_n; //Alert output

//Data Signals
wire [DWIDTH-1:0] pin_dq; //Bidirectional Data Bus
wire dbi_n, udbi_n, ldbi_n; //Data Bus Inversion
wire dqs_t,dqs_c,   //Data Strobe pins
	 dqsu_t,dqsu_c,
	 dqsl_t,dqsl_u;
wire tdqs_t,tdws_c; //Termination Data Strobe. 
logic [DWIDTH-1:0] dq_m, dq_c; ////Transaction Level Model(TLM) variable

/*****************************************************************/
//Assignments to pins from TLM variables
assign pin_dq = dq_m;
assign pin_A = A;
assign pin_dq = dq_c;
assign reset_n = ~reset;

//Modport Definitions
modport Memory	(
					import IsActivate, IsRefresh, IsWrite, IsRead, IsWriteA, IsReadA, IsPrePreA,
					import ReadRowBank, ReadColumnBank,
					input  cke,cs_n,dm_n,udm_n,ldm_n,odt,
						   par,reset_n,ten,pin_A,act_n,bg,
						   b,clk_t,clk_c,clock,
					output alert_n,tdqs_t,tdws_c,dq_m,
					inout  pin_dq,dbi_n,udbi_n,ldbi_n,dqs_t,dqs_c
				);

modport Controller	(
						import 	ACT,MRS,REF,PRE,PREA,WR,RD,WRA,RDA,NOP,DES,	
						output 	cke,cs_n,dm_n,udm_n,ldm_n,odt,
						   		par,ten,pin_A,act_n,bg,
						   		b,clk_t,clk_c,dq_c,
						input 	alert_n,tdqs_t,tdws_c,reset_n,
						inout  	pin_dq,dbi_n,udbi_n,ldbi_n,dqs_t,dqs_c
					);

/**************************CONTROLLER METHODS**********************************/
//Bank Activate
function automatic void ACT (input logic [/*AWIDTH-1*/14:0]Row_Address, 
						logic [BG_BITS-1:0] bankgrp,
						logic [B_BITS-1:0] bank);
	$display($time, "\tACTIVATE\tRow Address:%b",Row_Address);
	bg = bankgrp; b = bank;
	{cs_n,act_n} = LOW;
	cke = `HIGH;
	A[14:0] = Row_Address;

endfunction

//Mode Register Set(MRS) access
function automatic void MRS (input logic [2:0] MrsSelect, logic [13:0] code);
	$display($time, "\tMRS");	
	{bg[0],b} = MrsSelect;
	{cs_n,`RAS,`CAS,`WE} = LOW;
	act_n = `HIGH;
	bg[1] = 1'b0;
	A[17] = 1'b0;
	A[13:0] = code;
endfunction

//Refresh
function automatic void REF();
	$display($time, "\tREF");
	{cke,cs_n,act_n,`RAS,`CAS,`WE} = 6'b101000;
endfunction

//Precharge
function automatic void PRE (input 	logic [BG_BITS-1:0] bankgrp,
							 		logic [B_BITS-1:0] bank);
	$display($time, "\tPRECHARGE");
	{cke,act_n,`CAS} = `HIGH;
	{cs_n,`RAS,`WE,`AP} = LOW;
	bg = bankgrp; b = bank;
endfunction

//Auto-Precharge
function automatic void PREA();
	$display($time, "\tAUTO PRECHARGE");
	{cke,act_n,`CAS,`AP} = `HIGH;
	{cs_n,`RAS,`WE} = LOW;
endfunction

//Write
function automatic void WR (input logic [9:0] col_add,
								  logic [BG_BITS-1:0] bankgrp,
							 	  logic [B_BITS-1:0] bank);
	$display($time, "\tWRITE");	
	{cke,act_n,`RAS} = `HIGH;
	{cs_n,`CAS,`WE,`AP} = LOW;
	A[9:0] = col_add;
	bg = bankgrp; b = bank;
endfunction

//Read
function automatic void RD (input logic [9:0] col_add,
								  logic [BG_BITS-1:0] bankgrp,
							 	  logic [B_BITS-1:0] bank);

	$display($time, "\tREAD");	
	{cke,act_n,`RAS,`WE} = `HIGH;
	{cs_n,`CAS,`AP} = LOW;
	A[9:0] = col_add;
	bg = bankgrp; b = bank;
endfunction 

//Write with Precharge 
function automatic void WRA (input logic [9:0] col_add,
								  logic [BG_BITS-1:0] bankgrp,
							 	  logic [B_BITS-1:0] bank);
	$display($time, "\tWRITE WITH PRECHARGE\tColumn Address:%b",col_add);	
	{cke,act_n,`RAS,`AP} = `HIGH;
	{cs_n,`CAS,`WE} = LOW;
	A[9:0] = col_add;
	bg = bankgrp; b = bank;
endfunction

//Read with Precharge
function automatic void RDA (input logic [9:0] col_add,
								  logic [BG_BITS-1:0] bankgrp,
							 	  logic [B_BITS-1:0] bank);

	$display($time, "\tREAD WITH PRECHARGE");	
	{cke,act_n,`RAS,`WE,`AP} = `HIGH;
	{cs_n,`CAS} = LOW;
	A[9:0] = col_add;
	bg = bankgrp; b = bank;
endfunction 

//No-Operation
function automatic void NOP;
	$display($time, "\tNO OP");	
	{cke,act_n,`RAS,`CAS,`WE} = `HIGH;
	cs_n = LOW;
endfunction

//Deselect
function automatic void DES;
	$display($time, "\tDESELECT");	
	{cke,cs_n} = `HIGH;
endfunction

/****************************MEMORY METHODS*************************************/
function automatic bit IsActivate;
	bit IsBit;
	if(({cs_n,act_n} === LOW) && (cke === `HIGH))
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsActivate */

function automatic bit IsRefresh;
	bit IsBit;
	if ({cke,cs_n,act_n,`RAS,`CAS,`WE} === 6'b101000)
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsRefresh */

function automatic bit IsWrite;
	bit IsBit;
	if (({cke,act_n,`RAS} === `HIGH) && ({cs_n,`CAS,`WE,`AP} === LOW))
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsWrite */

function automatic bit IsRead;
	bit IsBit;
	if (({cke,act_n,`RAS,`WE} === `HIGH) && ({cs_n,`CAS,`AP} === LOW))
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsRead */

function automatic bit IsWriteA;
	bit IsBit;
	if (({cke,act_n,`RAS,`AP} === `HIGH) && ({cs_n,`CAS,`WE} === LOW))
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsWriteA */

function automatic bit IsReadA;
	bit IsBit;
	if (({cke,act_n,`RAS,`WE,`AP} === `HIGH) && ({cs_n,`CAS} === LOW))
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsReadA */

function automatic bit IsPrePreA;
	bit IsBit;
	if (({cke,act_n,`CAS} === `HIGH) && ({cs_n,`RAS,`WE} === LOW))
		IsBit = 1'b1;
	return IsBit;
endfunction /* IsPrePreA */

function automatic logic[15 + B_BITS + BG_BITS-1:0] ReadRowBank;
	$display($time,"\tROW:%b\tBANK:%x\tBG:%x",pin_A[14:0],b,bg);
	assert ($isunknown(pin_A[14:0])==0)
		else $warning("The row address isnt read correctly");
	return {pin_A[14:0],b,bg};
endfunction /* ReadRowBank */

function automatic logic[10 + BG_BITS + B_BITS-1:0] ReadColumnBank;
	$display($time,"\tThe cloumn address read is: %b",pin_A[9:0]);
	assert ($isunknown(pin_A[9:0])==0)
		else $warning("The column address isnt read correctly");
	return {A[9:0],b,bg};
endfunction /* ReadColumnBank */

//////////////////////ASSSERTIONS//////////////////////////////////
property Act_RW;
@(posedge clock)
	 ((cs_n === LOW) && (cke === `HIGH) && $fell(act_n))|-> ##TRCD ($fell(`CAS) || $rose(act_n));
endproperty

assert property(Act_RW)
	else $warning("TRCD Violation");

sequence S1;
@(edge clock)
($rose(act_n) && ({cke,`RAS} === `HIGH) && ({cs_n,`CAS,`AP} === LOW));
endsequence

property RW_to_Data;
@(edge clock)
S1|-> ##(2*TCL) (!$isunknown(pin_dq));
endproperty

assert property(RW_to_Data)
	else $warning("TCL violation");

endinterface

///////////////////////////////////////////////////////////////////////////