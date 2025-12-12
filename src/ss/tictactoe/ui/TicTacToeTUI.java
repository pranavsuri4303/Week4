package ss.tictactoe.ui;

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
        
        System.out.print("Enter name for Player 1: ");
        String name1 = scanner.next();
        
        System.out.print("Enter name for Player 2: ");
        String name2 = scanner.next();

        Player p1 = new HumanPlayer(name1, scanner);
        Player p2 = new HumanPlayer(name2, scanner);

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

            System.out.print("Play another game? (y/n): ");
            String answer = scanner.next();
            if (!answer.equalsIgnoreCase("y")) {
                play = false;
            }
        }
        System.out.println("Goodbye!");
    }
}