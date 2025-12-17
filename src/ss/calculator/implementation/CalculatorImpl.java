package ss.calculator.implementation;

import ss.calculator.Calculator;
import ss.calculator.DivideByZeroException;
import ss.calculator.StackEmptyException;

import java.util.ArrayDeque;
import java.util.Deque;

public class CalculatorImpl implements Calculator {

    private final Deque<Double> stack = new ArrayDeque<>();

    @Override
    public void push(double value) {
        stack.push(value);
    }

    @Override
    public double pop() throws StackEmptyException {
        if (stack.isEmpty()) {
            throw new StackEmptyException("Cannot pop from an empty stack.");
        }
        return stack.pop();
    }

    @Override
    public void add() throws StackEmptyException {
        if (stack.size() < 2) {
            throw new StackEmptyException("Not enough elements on the stack for add operation.");
        }
        double val1 = stack.pop();
        double val2 = stack.pop();
        stack.push(val2 + val1);
    }

    @Override
    public void sub() throws StackEmptyException {
        if (stack.size() < 2) {
            throw new StackEmptyException("Not enough elements on the stack for sub operation.");
        }
        double a = stack.pop();
        double b = stack.pop();
        stack.push(b - a);
    }

    @Override
    public void mult() throws StackEmptyException {
        if (stack.size() < 2) {
            throw new StackEmptyException("Not enough elements on the stack for mult operation.");
        }
        double val1 = stack.pop();
        double val2 = stack.pop();
        stack.push(val2 * val1);
    }

    @Override
    public void div() throws DivideByZeroException, StackEmptyException {
        if (stack.size() < 2) {
            throw new StackEmptyException("Not enough elements on the stack for div operation.");
        }
        double a = stack.pop();
        double b = stack.pop();
        if (a == 0) {
            stack.push(Double.NaN);
            throw new DivideByZeroException("Division by zero.");
        }
        stack.push(b / a);
    }

    @Override
    public void dup() throws StackEmptyException {
        if (stack.isEmpty()) {
            throw new StackEmptyException("Cannot dup on an empty stack.");
        }
        stack.push(stack.peek());
    }

    @Override
    public void mod() throws DivideByZeroException, StackEmptyException {
        if (stack.size() < 2) {
            throw new StackEmptyException("Not enough elements on the stack for mod operation.");
        }
        double a = stack.pop();
        double b = stack.pop();
        if (a == 0) {
            stack.push(Double.NaN);
            throw new DivideByZeroException("Division by zero.");
        }
        stack.push(b % a);
    }
}