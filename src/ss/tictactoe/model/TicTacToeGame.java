package ss.tictactoe.model;

import java.util.ArrayList;
import java.util.List;

/**
 * A class to represent the Tic Tac Toe game.
 */
public class TicTacToeGame implements Game {
    private Board board;
    private Player player1;
    private Player player2;
    private Player current;

    /**
     * Creates a new Tic Tac Toe game with two players.
     * Player 1 plays with XX and starts the game.
     * Player 2 plays with OO.
     */
    public TicTacToeGame(Player player1, Player player2) {
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        this.current = player1;
    }

    /**
     * Creates a deep copy of the game.
     * @return a new TicTacToeGame with the same state
     */
    /*@ ensures \result != this;
        ensures \result instanceof TicTacToeGame;
     @*/
    public TicTacToeGame deepCopy() {
        TicTacToeGame copy = new TicTacToeGame(this.player1, this.player2);
        // Overwrite the empty board created by constructor with a deep copy of the current board
        copy.board = this.board.deepCopy();
        copy.current = this.current;
        return copy;
    }

    @Override
    public boolean isGameover() {
        return board.gameOver();
    }

    @Override
    public Player getTurn() {
        return current;
    }

    @Override
    public Player getWinner() {
        if (board.isWinner(Mark.XX)) {
            return player1;
        } else if (board.isWinner(Mark.OO)) {
            return player2;
        }
        return null;
    }

    @Override
    public List<TicTacToeMove> getValidMoves() {
        List<TicTacToeMove> moves = new ArrayList<>();
        if (isGameover()) {
            return moves;
        }

        Mark currentMark = (current == player1) ? Mark.XX : Mark.OO;
        for (int i = 0; i < Board.DIM * Board.DIM; i++) {
            if (board.isEmptyField(i)) {
                moves.add(new TicTacToeMove(currentMark, i));
            }
        }
        return moves;
    }

    @Override
    public boolean isValidMove(Move move) {
        if (!(move instanceof TicTacToeMove)) {
            return false;
        }
        TicTacToeMove ttm = (TicTacToeMove) move;
        if (isGameover()) {
            return false;
        }

        Mark currentMark = (current == player1) ? Mark.XX : Mark.OO;
        if (ttm.getMark() != currentMark) {
            return false;
        }

        return board.isField(ttm.getIndex()) && board.isEmptyField(ttm.getIndex());
    }

    @Override
    public void doMove(Move move) {
        if (isValidMove(move)) {
            TicTacToeMove ttm = (TicTacToeMove) move;
            board.setField(ttm.getIndex(), ttm.getMark());
            current = (current == player1) ? player2 : player1;
        }
    }

    @Override
    public String toString() {
        return board.toString() + "\n" +
                "Turn: " + current.toString();
    }
}