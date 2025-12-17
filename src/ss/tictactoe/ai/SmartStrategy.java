package ss.tictactoe.ai;

import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;
import ss.tictactoe.model.TicTacToeGame;

import java.util.ArrayList;
import java.util.List;

/**
 * A smart strategy for Tic Tac Toe.
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

        // If game is not TicTacToeGame, we cannot use deepCopy, so we fall back to all valid moves
        if (!(game instanceof TicTacToeGame)) {
             int index = (int) (Math.random() * validMoves.size());
             return validMoves.get(index);
        }

        for (Move move : validMoves) {
            // Simulate the move to see what happens
            TicTacToeGame copy = ((TicTacToeGame) game).deepCopy();
            copy.doMove(move); // After this, it is the opponent's turn in the copy

            // Check if the opponent can win immediately in this new state
            if (findWinningMove(copy) == null) {
                // If opponent cannot win immediately after this move, it is 'allowed'
                allowedMoves.add(move);
            }
        }

        // 3. Select a move
        // If we have allowed moves (that don't lead to instant loss), pick from them.
        // If allowedMoves is empty (opponent wins no matter what), pick from all valid moves.
        List<? extends Move> candidates = allowedMoves.isEmpty() ? validMoves : allowedMoves;
        
        if (candidates.isEmpty()) {
            return null; // Should not happen if game is not over
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
        if (!(game instanceof TicTacToeGame)) {
            return null;
        }

        List<? extends Move> moves = game.getValidMoves();
        for (Move move : moves) {
            TicTacToeGame copy = ((TicTacToeGame) game).deepCopy();
            copy.doMove(move);
            // After doing the move, check if the game has a winner. 
            // Since we just made a move, if there is a winner, it must be the current player.
            if (copy.getWinner() != null) {
                return move;
            }
        }
        return null;
    }
}