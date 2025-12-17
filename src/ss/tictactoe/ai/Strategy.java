package ss.tictactoe.ai;

import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;

/**
 * Interface for strategies to determine the next move for the Tic-Tac-Toe game.
 */
public interface Strategy {

    /**
     * Returns the name of the strategy.
     * @return the name of the strategy
     */
    /*@ ensures \result != null; @*/
    /*@ pure */
    public String getName();

    /**
     * Determines the next legal move, given the current state of the game.
     * @param game the current game
     * @return a next legal move
     */
    /*@ requires game != null;
        requires !game.isGameover();
        ensures game.isValidMove(\result);
    @*/
    public Move determineMove(Game game);
}