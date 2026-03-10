// Tic Tac Toe Game in SystemVerilog using Constraints
// A 3x3 board with constraint-based move generation

package tictactoe_pkg;
  typedef enum {EMPTY=0, X=1, O=2} cell_t;
  typedef enum {X_TURN=0, O_TURN=1, X_WIN=2, O_WIN=3, DRAW=4} game_state_t;
endpackage

import tictactoe_pkg::*;

class Move;
  rand bit [3:0] row;
  rand bit [3:0] col;
  
  // Constraints: row and col must be valid (0-2)
  constraint valid_position {
    row >= 0 && row < 3;
    col >= 0 && col < 3;
  }
  
  function new();
  endfunction
  
  function void print();
    $display("Move: row=%0d, col=%0d", row, col);
  endfunction
endclass

class Board;
  cell_t board[3][3];
  game_state_t state;
  int move_count;
  
  function new();
    reset();
  endfunction
  
  function void reset();
    for (int i = 0; i < 3; i++) {
      for (int j = 0; j < 3; j++) {
        board[i][j] = EMPTY;
      endfor
    endfor
    state = X_TURN;
    move_count = 0;
  endfunction
  
  function bit is_empty(int row, int col);
    return (board[row][col] == EMPTY);
  endfunction
  
  function bit place_move(int row, int col, cell_t player);
    if (!is_empty(row, col)) begin
      $display("ERROR: Cell (%0d,%0d) is not empty!", row, col);
      return 0;
    end
    board[row][col] = player;
    move_count++;
    return 1;
  endfunction
  
  function bit check_winner(cell_t player);
    // Check rows
    for (int i = 0; i < 3; i++) begin
      if (board[i][0] == player && board[i][1] == player && board[i][2] == player)
        return 1;
    end
    
    // Check columns
    for (int j = 0; j < 3; j++) begin
      if (board[0][j] == player && board[1][j] == player && board[2][j] == player)
        return 1;
    end
    
    // Check diagonals
    if (board[0][0] == player && board[1][1] == player && board[2][2] == player)
      return 1;
    if (board[0][2] == player && board[1][1] == player && board[2][0] == player)
      return 1;
    
    return 0;
  endfunction
  
  function void update_state();
    if (check_winner(X))
      state = X_WIN;
    else if (check_winner(O))
      state = O_WIN;
    else if (move_count == 9)
      state = DRAW;
    else
      state = (state == X_TURN) ? O_TURN : X_TURN;
  endfunction
  
  function void display();
    string row_str;
    $display("\n=== Board State ===");
    for (int i = 0; i < 3; i++) begin
      row_str = "";
      for (int j = 0; j < 3; j++) begin
        case (board[i][j])
          X: row_str = {row_str, " X "};
          O: row_str = {row_str, " O "};
          EMPTY: row_str = {row_str, " . "};
        endcase
        if (j < 2) row_str = {row_str, "|"};
      end
      $display(row_str);
      if (i < 2) $display("-----------");
    end
    $display("===================\n");
  endfunction
  
  function string get_state_string();
    case (state)
      X_TURN: return "X's Turn";
      O_TURN: return "O's Turn";
      X_WIN: return "X Wins!";
      O_WIN: return "O Wins!";
      DRAW: return "Game is a Draw";
      default: return "Unknown State";
    endcase
  endfunction
endclass

class Game;
  Board board;
  Move move;
  int max_iterations = 100;
  int iteration = 0;
  
  function new();
    board = new();
    move = new();
  endfunction
  
  function bit play_random_game();
    cell_t current_player;
    
    $display("===== STARTING TIC TAC TOE GAME =====\n");
    board.display();
    
    while (iteration < max_iterations) begin
      iteration++;
      
      // Determine current player
      current_player = (board.state == X_TURN) ? X : O;
      
      // Generate random move with constraints
      if (!move.randomize()) begin
        $display("ERROR: Failed to randomize move");
        return 0;
      end
      
      // Check if cell is empty, if not, re-randomize
      while (!board.is_empty(move.row, move.col)) begin
        if (!move.randomize()) begin
          $display("ERROR: No valid moves remaining");
          return 0;
        end
      end
      
      $display("Move %0d: Player %s plays at (%0d, %0d)", 
               board.move_count + 1, 
               (current_player == X) ? "X" : "O",
               move.row, move.col);
      
      board.place_move(move.row, move.col, current_player);
      board.display();
      
      // Update game state
      board.update_state();
      
      // Check if game is over
      if (board.state == X_WIN) begin
        $display("*** %s ***", board.get_state_string());
        return 1;
      end
      else if (board.state == O_WIN) begin
        $display("*** %s ***", board.get_state_string());
        return 1;
      end
      else if (board.state == DRAW) begin
        $display("*** %s ***", board.get_state_string());
        return 1;
      end
    end
    
    return 1;
  endfunction
  
  function void reset();
    board.reset();
    iteration = 0;
  endfunction
endclass

module tictactoe_tb;
  Game game;
  
  initial begin
    game = new();
    
    // Play multiple games
    for (int g = 0; g < 3; g++) begin
      $display("\n\n");
      $display("╔════════════════════════════════╗");
      $display("║        GAME %0d                  ║", g+1);
      $display("╚════════════════════════════════╝");
      game.play_random_game();
      game.reset();
    end
    
    $finish;
  end
endmodule
