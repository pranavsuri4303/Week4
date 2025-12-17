package ss.tictactoe.ai;

import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;

import java.util.List;

/**
 * A naive strategy that returns a random valid move.
 */
public class NaiveStrategy implements Strategy {

    /**
     * Returns the name of the strategy.
     * @return "Naive"
     */
    @Override
    public String getName() {
        return "Naive";
    }

    /**
     * Determines the next legal move, given the current state of the game.
     * Randomly selects a move from the available valid moves.
     * @param game the current game
     * @return a randomly selected valid move
     */
    @Override
    public Move determineMove(Game game) {
        List<? extends Move> validMoves = game.getValidMoves();
        int index = (int) (Math.random() * validMoves.size());
        return validMoves.get(index);
    }
}