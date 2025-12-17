package ss.tictactoe.ui;

import ss.tictactoe.ai.ComputerPlayer;
import ss.tictactoe.ai.NaiveStrategy;
import ss.tictactoe.ai.SmartStrategy;
import ss.tictactoe.ai.Strategy;
import ss.tictactoe.model.*;

import java.util.Scanner;

/**
 * Text-based User Interface for Tic Tac Toe.
 */
public class TicTacToeTUI {

    public static void main(String[] args) {
        new TicTacToeTUI().run();
    }

    public void run() {
        Scanner scanner = new Scanner(System.in);
        System.out.println("Welcome to Tic Tac Toe!");

        // Setup Player 1 and Player 2 using the helper method
        Player p1 = setupPlayer(scanner, "Player 1", Mark.XX);
        Player p2 = setupPlayer(scanner, "Player 2", Mark.OO);

        boolean play = true;
        while (play) {
            Game game = new TicTacToeGame(p1, p2);

            while (!game.isGameover()) {
                System.out.println("\n" + game.toString());
                Player current = game.getTurn();
                if (current instanceof AbstractPlayer) {
                    Move move = ((AbstractPlayer) current).determineMove(game);
                    game.doMove(move);
                }
            }

            System.out.println("\n" + game.toString());
            Player winner = game.getWinner();
            if (winner != null) {
                System.out.println("Winner: " + ((AbstractPlayer) winner).getName());
            } else {
                System.out.println("Draw!");
            }

            play = getBooleanInput(scanner, "Play another game? (y/n): ");
        }
        System.out.println("Goodbye!");
    }

    /**
     * Helper method to setup a player (Human or Computer).
     */
    private Player setupPlayer(Scanner scanner, String promptName, Mark mark) {
        boolean isComputer = getBooleanInput(scanner, "Is " + promptName + " a computer? (y/n): ");
        if (isComputer) {
            Strategy strategy = getStrategyFromInput(scanner);
            return new ComputerPlayer(mark, strategy);
        } else {
            System.out.print("Enter name for " + promptName + ": ");
            String name = scanner.next();
            return new HumanPlayer(name, scanner);
        }
    }

    /**
     * Helper method to get the strategy choice from the user.
     */
    private Strategy getStrategyFromInput(Scanner scanner) {
        while (true) {
            System.out.print("Select strategy (Naive/Smart): ");
            String input = scanner.next();
            if (input.equalsIgnoreCase("Naive")) {
                return new NaiveStrategy();
            } else if (input.equalsIgnoreCase("Smart")) {
                return new SmartStrategy();
            } else {
                System.out.println("Invalid strategy. Please enter 'Naive' or 'Smart'.");
            }
        }
    }

    /**
     * Helper method to ensure the user enters 'y' or 'n'.
     */
    private boolean getBooleanInput(Scanner scanner, String prompt) {
        while (true) {
            System.out.print(prompt);
            String input = scanner.next();
            if (input.equalsIgnoreCase("y")) {
                return true;
            } else if (input.equalsIgnoreCase("n")) {
                return false;
            } else {
                System.out.println("Invalid input. Please enter 'y' or 'n'.");
            }
        }
    }
}