package ss.tictactoe.ai;

import ss.tictactoe.model.AbstractPlayer;
import ss.tictactoe.model.Game;
import ss.tictactoe.model.Mark;
import ss.tictactoe.model.Move;

/**
 * A computer player that uses a strategy to determine its moves.
 */
public class ComputerPlayer extends AbstractPlayer {

    private Strategy strategy;
    private final Mark mark;

    /**
     * Constructs a computer player using the given mark and strategy.
     * The name of the player is constructed as "StrategyName-Mark".
     *
     * @param mark     the mark of this player
     * @param strategy the strategy to use
     */
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(strategy.getName() + "-" + mark);
        this.mark = mark;
        this.strategy = strategy;
    }

    /**
     * Determines the next move by delegating to the strategy.
     *
     * @param game the current game
     * @return the move determined by the strategy
     */
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    /**
     * Returns the current strategy of this player.
     *
     * @return the current strategy
     */
    public Strategy getStrategy() {
        return strategy;
    }

    /**
     * Sets a new strategy for this player.
     *
     * @param strategy the new strategy to set
     */
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    /**
     * Returns the mark of this player.
     *
     * @return the mark
     */
    public Mark getMark() {
        return mark;
    }
}