typedef struct packed {
    logic [6:0] funct7;
    logic [4:0] rs2;
    logic [4:0] rs1;
    logic [2:0] funct3;
    logic [4:0] rd;
    logic [6:0] opcode;
} RISCVInstruction;

typedef struct packed {
    logic [11:0] immediate;
    logic [4:0]  rs1;
    logic [2:0]  funct3;
    logic [4:0]  rd;
    logic [6:0]  opcode;
} RISCVITypeInstruction;

typedef struct packed {
    logic [11:5] immediate;
    logic [4:0]  rs2;
    logic [4:0]  rs1;
    logic [2:0]  funct3;
    logic [4:0] immediate;
    logic [6:0]  opcode;
} RISCVSTypeInstruction;