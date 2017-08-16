//This file handles the communication between the memory controller and the \
//Cache BFM with respect to the data read by the controller from the memory.
//Send_read_data is used by the controller
//receive_read_data is used by the cache bfm
//Author: Niraj Thakkar
module send_read_data  
(	
	C2MInterface.Mem_data IF, 
	input logic internal_ready,
				[IF.DWIDTH-1:0]data_in, 
				[2:0] tag_gen
);

assign IF.read_data = (internal_ready)?data_in:'z;
assign IF.tag_data = (internal_ready)?tag_gen:'z;
assign IF.valid_data = internal_ready;

endmodule

module receive_read_data  
(C2MInterface.Cache_data IF,output logic read_valid, [IF.DWIDTH-1:0] data_out,[2:0] tag_out);

assign data_out = IF.read_data;
assign tag_out = IF.tag_data;
assign read_valid = IF.valid_data;

endmodule
