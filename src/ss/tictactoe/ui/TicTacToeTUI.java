package ss.tictactoe.ui;

import ss.tictactoe.ai.ComputerPlayer;
import ss.tictactoe.ai.NaiveStrategy;
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

        // Setup Player 1
        Player p1;
        boolean p1IsComputer = getBooleanInput(scanner, "Is Player 1 a computer? (y/n): ");

        if (p1IsComputer) {
            // Player 1 uses Mark.XX
            p1 = new ComputerPlayer(Mark.XX, new NaiveStrategy());
        } else {
            System.out.print("Enter name for Player 1: ");
            String name1 = scanner.next();
            p1 = new HumanPlayer(name1, scanner);
        }

        // Setup Player 2
        Player p2;
        boolean p2IsComputer = getBooleanInput(scanner, "Is Player 2 a computer? (y/n): ");

        if (p2IsComputer) {
            // Player 2 uses Mark.OO
            p2 = new ComputerPlayer(Mark.OO, new NaiveStrategy());
        } else {
            System.out.print("Enter name for Player 2: ");
            String name2 = scanner.next();
            p2 = new HumanPlayer(name2, scanner);
        }

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

            // Use the helper method for the replay option as well
            play = getBooleanInput(scanner, "Play another game? (y/n): ");
        }
        System.out.println("Goodbye!");
    }

    /**
     * Helper method to ensure the user enters 'y' or 'n'.
     * loops until valid input is received.
     * * @param scanner the scanner to read from
     * @param prompt  the message to display to the user
     * @return true if user entered 'y', false if 'n'
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