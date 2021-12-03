package c0.virtual.machine;

import java.io.IOException;

/**
 * Front-end for a C<sub>0</sub> virtual machine. Allows command-line usage of
 * the virtual machine.
 *
 * @author Trey Stevens
 */
public class C0VirtualMachine {

    public static void main(String[] args) throws IOException {
        System.out.println(C0VM.run(args[args.length - 1]));
    }

}
