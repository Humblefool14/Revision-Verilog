package definitions;
  typedef enum{ADD,SUB,MUL,DIV,SL,SR}opcode_t;
  typedef enum{unsigned,signed} operand_t;
  typedef union packed{ 
    logic [31:0]u_data;
    logic signed [31:0]s_data;
  } data_t;
  typedef struct packed{
    opcode_t opcode;
    data_t data_a;
    data_t data_b;
    operand_t operand;
  } instruction_t;
end package;
  
  module(input a,input b,input c){
    
    
    
