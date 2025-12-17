package ss.tictactoe.model;

import java.util.Objects;

/**
 * A move in the Tic Tac Toe game.
 */
public class TicTacToeMove implements Move {
    private final Mark mark;
    private final int index;

    public TicTacToeMove(Mark mark, int index) {
        this.mark = mark;
        this.index = index;
    }

    public Mark getMark() {
        return mark;
    }

    public int getIndex() {
        return index;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TicTacToeMove that = (TicTacToeMove) o;
        return index == that.index && mark == that.mark;
    }

    @Override
    public int hashCode() {
        return Objects.hash(mark, index);
    }

    @Override
    public String toString() {
        return "Move{" + mark + ", " + index + "}";
    }
}