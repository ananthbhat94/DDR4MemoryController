//Top Module which instantiates the controller, Memory BFM and Cache BFM
//Basic testbench is used.
//Self checking capabilities included.
//Author: Shivank Dhote
`timescale 1ps/1ps
module Top();
logic clock,clock2x,Reset,rw,go;
logic [31:0] Address;
logic [511:0] Data;
logic [511:0] DataController;

//Initialize variables needed
logic [7:0][31:0]MemoryTb;
logic [31:0] address;
logic operation, valid;
logic [(32*16)-1:0] data_out, data_in;
logic full, ack_in,ack_out;
logic[2:0] tag_in,tag_out;
logic [31:0] receivedvalue,errorvalue,sentvalue;
logic control,flag;

/********Clock Generator************/
//Clock1x Generator
initial begin
clock = 1'b1;
Reset = 1'b1;
Data = 'z;
forever #10 clock = ~clock;
end

//Clock2x Generator
initial begin
clock2x=1'b1;
forever #5 clock2x = ~clock2x;
end

//Function to Write to the Memory Controller
task Write(input logic [31:0] data);
	control = 1'b1;
	sentvalue = data;
	@(negedge clock);
	while (flag==1'b1)
		@(negedge clock);
	control = 1'b0;
	@(negedge clock);
endtask

//Basic Testbench to check initial working.
//More exhaustive testing is done in another TB, 
//but its written with respect to the emulator.
initial begin
	repeat (5) @(negedge clock);
	$display ($time, "\tReset is now off");
	Reset = 1'b0;
	Write(32'b000000000000001_00_0000000_00_000_000);
	Write(32'b000000000000010_00_0000000_01_000_000);
	Write(32'b100000000000010_00_0000000_01_000_000);
	Write(32'b000000000000001_00_0001000_00_000_000);
	repeat (200) @(negedge clock);
	$finish;

end

//XRTL FSM to obtain operands from the HVL side(Emulation)
always@(posedge clock)
begin
	if(Reset)
    begin
		address <= {32{1'b0}};
		data_in <= {(32*2){1'b0}};
		operation <= {32{1'b0}};
		valid <= 1'b0;       
		flag <= 1'b0;
	end
	else if(!control)
		valid <= 1'b0;
    else if(!full)
        begin
       		if((!ack_in) && (!flag))
			begin
				address <= {0,sentvalue[30:0]};
				data_in <= {16{sentvalue}};
				operation <= sentvalue >> 31;
                valid <= 1'b1;
				flag <=1;	
				$strobe($time,"\t%m\tAddress Sent:%x:", address);
			end
			else if (ack_in)
			begin
				valid <= 1'b0;
				$display($time,"\t%m\tThe tag received is:%0d",tag_in);
				MemoryTb[tag_in] <= sentvalue;
				flag <= 1'b0;
			end
			else begin
				address <= sentvalue;
				data_in <= {16{sentvalue}};
				operation <= sentvalue >> 31;
                valid <= 1'b1;
			end
		end
	else
    begin
		valid <=0;
		flag <= 0;
    end            
end
	
	always@(posedge clock)
	begin
		if(ack_out)
		begin
		receivedvalue <= data_out[31:0];
		errorvalue <= 32'hFFFFFFFF;
			if(receivedvalue === MemoryTb[tag_out])
				$display("The Data Read has matched");
			else
				$display("The Data Read hasnt matched");
		end
	end



//initial 
//	$monitor($time,"\tACT:%b\tCS:%b\tCKE:%b\tAddress:%h\tData:%x\tDone:%x\tStart:%x",DDR4Bus.act_n,DDR4Bus.cs_n,DDR4Bus.cke,sentvalue,DDR4Bus.pin_dq,C.S.done,C.S.start);
//	$monitor($time,"\tACK_IN:%x,FLAG:%x,ACK_OUT:%x,Address:%x\tcontrol:%x\tvalid:%x\tvalid_xrtl:%x\tfull:%0d",ack_in,flag,ack_out,address,control,valid,sc.valid_xrtl,full);
/*
final 
	$display("Full is : %0d",full);
*/
//Instantiate the DDR4Interface
DDR4Interface DDR4Bus (clock,Reset);

//Instantiate The C2M Bus
C2MInterface C2MBus (clock,Reset);

//Instantiate The Memory BFM
Memory M (DDR4Bus.Memory,clock2x);

//Instantiate the Memory Controller
MemoryController C (.clock2x, .clock, .reset(Reset), .DDR4Bus(DDR4Bus.Controller),.MCTx(C2MBus.Mem_data),.MCRx(C2MBus.Mem_tran));

receive_read_data rrd (C2MBus, ack_out, data_out, tag_out);
send_command sc (C2MBus, operation, valid, data_in,address, ack_in, full,tag_in);
	
endmodule
