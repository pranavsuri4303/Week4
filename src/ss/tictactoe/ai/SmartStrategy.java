package ss.tictactoe.ai;

import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;

import java.util.ArrayList;
import java.util.List;

/**
 * A smart strategy for Tic Tac Toe (or any Game).
 * 1. Wins immediately if possible.
 * 2. Blocks the opponent if they can win in the next turn.
 * 3. Otherwise, picks a random valid move.
 */
public class SmartStrategy implements Strategy {

    @Override
    public String getName() {
        return "Smart";
    }

    @Override
    public Move determineMove(Game game) {
        // 1. Try to find a direct winning move
        Move winningMove = findWinningMove(game);
        if (winningMove != null) {
            return winningMove;
        }

        // 2. If no winning move, find moves that prevent the opponent from winning next turn
        List<Move> allowedMoves = new ArrayList<>();
        List<? extends Move> validMoves = game.getValidMoves();

        for (Move move : validMoves) {
            // Polymorphism in action: we don't care if it's TicTacToe or Chess
            Game copy = game.deepCopy();
            copy.doMove(move);

            // Check if the opponent can win immediately in this new state
            if (findWinningMove(copy) == null) {
                // If opponent cannot win immediately after this move, it is 'allowed'
                allowedMoves.add(move);
            }
        }

        // 3. Select a move
        List<? extends Move> candidates = allowedMoves.isEmpty() ? validMoves : allowedMoves;

        if (candidates.isEmpty()) {
            return null;
        }

        int index = (int) (Math.random() * candidates.size());
        return candidates.get(index);
    }

    /**
     * Helper method to find a winning move for the current player in the given game state.
     * @param game the game to check
     * @return a winning move, or null if none exists
     */
    private Move findWinningMove(Game game) {
        List<? extends Move> moves = game.getValidMoves();
        for (Move move : moves) {
            Game copy = game.deepCopy();
            copy.doMove(move);

            if (copy.getWinner() != null) {
                return move;
            }
        }
        return null;
    }
}