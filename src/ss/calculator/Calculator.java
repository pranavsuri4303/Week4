package ss.calculator;

/**
 * A stack-based calculator supporting just the operations push/pop, add, sub, mult, div.
 */
public interface Calculator {
    /**
     * Push the given value on the stack.
     * @param value the value to push on the stack
     */
    void push(double value);

    /**
     * Pop a value from the stack.
     * @return the value that was on the top of the stack
     * @throws StackEmptyException if the stack is empty
     */
    double pop() throws StackEmptyException;

    /**
     * Remove two values from the top of the stack, add them, then push the result on top of the stack.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    void add() throws StackEmptyException;

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b-a and push the result on top of the stack
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    void sub() throws StackEmptyException;

    /**
     * Remove two values from the top of the stack, multiply them, then push the result on top of the stack
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    void mult() throws StackEmptyException;

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b/a  and push the result on top of the stack
     * If a was zero, then push the value "Double.NaN" on top of the stack and throw the exception.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     * @throws DivideByZeroException if value a had value 0
     */
    void div() throws DivideByZeroException, StackEmptyException;

    /**
     * Duplicate the value on top of the stack.
     * For example, if the value on top of the stack is 123, push another 123 on top of the stack.
     * @throws StackEmptyException if the stack is empty
     */
    void dup() throws StackEmptyException;

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b % a (remainder) and push the result on top of the stack.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    void mod() throws DivideByZeroException, StackEmptyException;
}
