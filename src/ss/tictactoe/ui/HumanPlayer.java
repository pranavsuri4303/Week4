package ss.tictactoe.ui;

import ss.tictactoe.model.AbstractPlayer;
import ss.tictactoe.model.Game;
import ss.tictactoe.model.Move;
import ss.tictactoe.model.TicTacToeMove;

import java.util.List;
import java.util.Scanner;

/**
 * A human player for Tic Tac Toe.
 */
public class HumanPlayer extends AbstractPlayer {

    private final Scanner scanner;

    public HumanPlayer(String name, Scanner scanner) {
        super(name);
        this.scanner = scanner;
    }

    @Override
    public Move determineMove(Game game) {
        System.out.println(getName() + " (" + (game.getTurn() == this ? "your turn" : "waiting") + "), please enter your move index (0-8): ");

        while (true) {
            if (scanner.hasNextInt()) {
                int index = scanner.nextInt();
                List<? extends Move> validMoves = game.getValidMoves();
                for (Move move : validMoves) {
                    if (move instanceof TicTacToeMove) {
                        if (((TicTacToeMove) move).getIndex() == index) {
                            return move;
                        }
                    }
                }
            } else {
                scanner.next(); // Consume invalid input
            }
            System.out.println("Invalid move. Please try again (0-8): ");
        }
    }
}