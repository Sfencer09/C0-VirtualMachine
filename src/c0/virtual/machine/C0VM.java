package c0.virtual.machine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.StreamTokenizer;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.StringTokenizer;

/**
 * A virtual machine for running C<sub>0</sub> code from a compiled .bc0
 * bytecode file.
 *
 * @author Trey Stevens
 */
public class C0VM {

    public C0VM(File source) throws IOException {
        if (!source.isFile() || !source.getName().endsWith(".bc0")) {
            throw new IOException("File is not a bytecode file");
        }
        this.src = source;
        this.heap = new Heap();
        this.parse();
    }

    public final class SegmentationFault extends RuntimeException {

        SegmentationFault() {
        }

        SegmentationFault(String message) {
            super(message);
        }

    }

    /**
     * Because Java does not have explicit pointers or the functionality that
     * comes with them, this class aims to replicate that functionality by
     * acting as a virtual heap, with methods for allocating, reading from, and
     * writing to blocks of memory.
     */
    private final class Heap {

        private byte[] mem;
        private int[] allocated;
        private int nextUnallocated = 0;
        static final int NULL = -1;

        /**
         * Constructs a new heap with an initial size of 64 kb and no bytes
         * allocated.
         */
        Heap() {
            this.mem = new byte[64000];
            this.allocated = new int[2000];
        }

        private boolean isAllocated(int addr) {
            if (addr < 0 || addr >= mem.length) {
                return false;
            }
            return (allocated[addr / 32] & (1 << (addr % 32))) != 0;
        }

        private void markAllocated(int addr) {
            assert (!isAllocated(addr));
            allocated[addr / 32] |= 1 << (addr % 32);
        }

        /**
         * Allocates a specific number of bytes on the heap and returns the
         * index of the first allocated
         *
         * @param numBytes
         * @return
         */
        int allocate(int numBytes) {
            if (numBytes <= 0) {
                throw new IllegalArgumentException();
            }
            while (nextUnallocated + numBytes >= mem.length) {
                expand();
            }
            int addr = nextUnallocated;
            for (int i = 0; i < numBytes; i++) {
                markAllocated(nextUnallocated++);
            }
            nextUnallocated++; //leave a 1-byte space in-between allocated
            //  blocks to reduce the chances of memory errors going undetected
            //  at runtime
            return addr;
        }

        private void expand() {
            byte[] newMem = new byte[mem.length + 8000];
            int[] newAlloc = new int[allocated.length + 250];
            System.arraycopy(mem, 0, newMem, 0, mem.length);
            System.arraycopy(allocated, 0, newAlloc, 0, allocated.length);
            this.mem = newMem;
            this.allocated = newAlloc;
            System.gc();
        }

        void write(int addr, byte... newVal) {
            if (newVal == null || newVal.length == 0) {
                throw new IllegalArgumentException("attempted to write 0 bytes to heap");
            }
            if (addr == NULL) {
                throw new SegmentationFault();
            }
            for (int i = 0; i < newVal.length; i++) {
                if (!isAllocated(addr + i)) {
                    throw new SegmentationFault();
                }
                mem[addr + i] = newVal[i];
            }
        }

        void writeInt(int addr, int newVal) {
            byte[] newBytes = new byte[4];
            for (int i = 3; i >= 0; i--) {
                newBytes[i] = (byte) (newVal & 0xFF);
                newVal >>= 8;
            }
            write(addr, newBytes);
        }

        byte[] read(int addr, int numBytes) {
            if (numBytes <= 0) {
                throw new IllegalArgumentException();
            }
            if (addr == NULL) {
                throw new SegmentationFault();
            }
            byte[] bytesRead = new byte[numBytes];
            for (int i = 0; i < numBytes; i++) {
                if (!isAllocated(addr + i)) {
                    throw new SegmentationFault();
                }
                bytesRead[i] = mem[addr + i];
            }
            return bytesRead;
        }

        int readInt(int addr) {
            byte[] intBytes = read(addr, 4);
            int i = 0;
            for (int j = 0; j < 4; j++) {
                i <<= 8;
                i |= (((int) intBytes[j]) & 0x000000FF);
            }
            return i;
        }

        /**
         * Frees all the bytes held by this heap, resets the size back to 64 kb,
         * and calls {@code System.gc()} to free the physical memory that had
         * been used by this virtual heap.
         */
        void freeAll() {
            mem = new byte[64000];
            allocated = new int[2000];
            System.gc();
        }
    }

    private static final int C0_INTEGER = 1;
    private static final int C0_POINTER = 2;

    public static PrintStream autoGrader = System.err;

    private final class c0_value {

        final int kind;
        final int val;

        c0_value(int kind, int value) {
            this.kind = kind;
            this.val = value;
        }
    }

    private final class Function {

        final short numArgs;
        final short numVars;
        final int codeSize;
        final byte[] code;

        Function(short numArgs, short numVars, byte[] code) {
            if (numArgs < 0 || numArgs < 0 || numArgs > numVars) {
                throw new IllegalArgumentException();
            }
            this.numArgs = numArgs;
            this.numVars = numVars;
            this.code = code;
            this.codeSize = code.length;
        }
    }

    private final class stackFrame {

        byte[] P;
        int pc;
        Deque<c0_value> S;
        c0_value[] V;

        stackFrame(byte[] P, int pc, Deque<c0_value> S, c0_value[] V) {
            this.P = P;
            this.S = S;
            this.V = V;
            this.pc = pc;
        }
    }

    private final File src;
    private final Heap heap;
    private int magic;
    private short version;
    private short intCount;
    private int[] intPool;
    private short stringCount;
    private byte[] stringPool;
    private short functionCount;
    private Function[] functionPool;
    private short nativeCount;
    private short[] nativeArgCounts;
    private short[] nativeIDs;

    private static final byte IADD = 0x60,
            IAND = 0x7E,
            IDIV = 0x6C,
            IMUL = 0x68,
            IOR = (byte) 0x80,
            IREM = 0x70,
            ISHL = 0x78,
            ISHR = 0x7A,
            ISUB = 0x64,
            IXOR = (byte) 0x82,
            DUP = 0x59,
            POP = 0x57,
            SWAP = 0x5F,
            NEWARRAY = (byte) 0xBC,
            ARRAYLENGTH = (byte) 0xBE,
            NEW = (byte) 0xBB,
            AADDF = 0x62,
            AADDS = 0x63,
            IMLOAD = 0x2E,
            AMLOAD = 0x2F,
            IMSTORE = 0x4E,
            AMSTORE = 0x4F,
            CMLOAD = 0x34,
            CMSTORE = 0x55,
            VLOAD = 0x15,
            VSTORE = 0x36,
            ACONST_NULL = 0x01,
            BIPUSH = 0x10,
            ILDC = 0x13,
            ALDC = 0x14,
            NOP = 0x00,
            IF_CMPEQ = (byte) 0x9F,
            IF_CMPNE = (byte) 0xA0,
            IF_ICMPLT = (byte) 0xA1,
            IF_ICMPGE = (byte) 0xA2,
            IF_ICMPGT = (byte) 0xA3,
            IF_ICMPLE = (byte) 0xA4,
            GOTO = (byte) 0xA7,
            ATHROW = (byte) 0xBF,
            ASSERT = (byte) 0xCF,
            INVOKESTATIC = (byte) 0xB8,
            INVOKENATIVE = (byte) 0xB7,
            RETURN = (byte) 0xB0;

    private void parse() throws IOException {
        StreamTokenizer st = new StreamTokenizer(new FileReader(src));
        st.commentChar('#');
        st.eolIsSignificant(false);
        st.lowerCaseMode(false);
        st.ordinaryChars('0', '9');
        st.wordChars('0', '9');
        st.wordChars('A', 'F');
        st.wordChars('a', 'f');
        st.whitespaceChars(0, 32);
        StringBuilder temp = new StringBuilder(8);
        for (int i = 0; i < 4; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            temp.append(st.sval);
        }
        assert temp.toString().equalsIgnoreCase("C0C0FFEE");
        this.magic = (int) Long.parseLong(temp.toString(), 16);
        temp.delete(0, 8);
        for (int i = 0; i < 2; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            temp.append(st.sval);
        }
        assert temp.length() == 4;
        this.version = (short) Integer.parseInt(temp.toString(), 16);
        temp.delete(0, 4);
        for (int i = 0; i < 2; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            temp.append(st.sval);
        }
        assert temp.length() == 4;
        this.intCount = (short) Integer.parseInt(temp.toString(), 16);
        temp.delete(0, 4);
        this.intPool = new int[this.intCount];
        for (int i = 0; i < this.intCount; i++) {
            for (int j = 0; j < 4; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                temp.append(st.sval);
            }
            assert temp.length() == 8;
            intPool[i] = (int) Long.parseLong(temp.toString(), 16);
            temp.delete(0, 8);
        }
        for (int i = 0; i < 2; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            temp.append(st.sval);
        }
        assert temp.length() == 4;
        this.stringCount = (short) Integer.parseInt(temp.toString(), 16);
        this.stringPool = new byte[this.stringCount];
        temp.delete(0, 4);
        for (int i = 0; i < this.stringCount; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            stringPool[i] = (byte) Integer.parseInt(st.sval, 16);
        }
        for (int i = 0; i < 2; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            temp.append(st.sval);
        }
        assert temp.length() == 4;
        this.functionCount = (short) Integer.parseInt(temp.toString(), 16);
        this.functionPool = new Function[this.functionCount];
        temp.delete(0, 4);
        for (int i = 0; i < this.functionCount; i++) {
            for (int j = 0; j < 2; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                temp.append(st.sval);
            }
            assert temp.length() == 4;
            short argCount = (short) Integer.parseInt(temp.toString(), 16);
            temp.delete(0, 4);
            for (int j = 0; j < 2; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                temp.append(st.sval);
            }
            assert temp.length() == 4;
            short varCount = (short) Integer.parseInt(temp.toString(), 16);
            temp.delete(0, 4);
            for (int j = 0; j < 2; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                temp.append(st.sval);
            }
            assert temp.length() == 4;
            short codeLength = (short) Integer.parseInt(temp.toString(), 16);
            temp.delete(0, 4);
            byte[] bytecode = new byte[codeLength];
            for (int j = 0; j < codeLength; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                bytecode[j] = (byte) Integer.parseInt(st.sval, 16);
            }
            this.functionPool[i] = new Function(argCount, varCount, bytecode);
        }
        for (int i = 0; i < 2; i++) {
            st.nextToken();
            assert st.ttype == StreamTokenizer.TT_WORD;
            temp.append(st.sval);
        }
        assert temp.length() == 4;
        this.nativeCount = (short) Integer.parseInt(temp.toString(), 16);
        temp.delete(0, 4);
        this.nativeIDs = new short[this.nativeCount];
        this.nativeArgCounts = new short[this.nativeCount];
        for (int i = 0; i < this.nativeCount; i++) {
            for (int j = 0; j < 2; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                temp.append(st.sval);
            }
            assert temp.length() == 4;
            this.nativeArgCounts[i] = (short) Integer.parseInt(temp.toString(), 16);
            temp.delete(0, 4);
            for (int j = 0; j < 2; j++) {
                st.nextToken();
                assert st.ttype == StreamTokenizer.TT_WORD;
                temp.append(st.sval);
            }
            assert temp.length() == 4;
            this.nativeIDs[i] = (short) Integer.parseInt(temp.toString(), 16);
            temp.delete(0, 4);
        }

        int stringPoolAddr = heap.allocate(stringCount);
        assert stringPoolAddr == 0;
        heap.write(stringPoolAddr, stringPool);
    }

    private int val2int(c0_value c) {
        assert c.kind == C0_INTEGER;
        return c.val;
    }

    private c0_value int2val(int i) {
        return new c0_value(C0_INTEGER, i);
    }

    private int val2ptr(c0_value c) {
        assert c.kind == C0_POINTER;
        return c.val;
    }

    private c0_value ptr2val(int p) {
        return new c0_value(C0_POINTER, p);
    }

    private void c0_arith_error(String msg) {
        throw new ArithmeticException(msg);
    }

    private void c0_memory_error(String msg) {
        throw new SegmentationFault(msg);
    }

    private void c0_user_error(int strAddr) {
        StringBuilder sb = new StringBuilder();
        byte b;
        for (int i = 0; (b = heap.read(strAddr + i, 1)[0]) != 0; i++) {
            sb.append((char) b);
        }
        throw new RuntimeException(sb.toString());
    }

    private void c0_assertion_failure(int strAddr) {
        StringBuilder sb = new StringBuilder();
        byte b;
        for (int i = 0; (b = heap.read(strAddr + i, 1)[0]) != 0; i++) {
            sb.append((char) b);
        }
        throw new RuntimeException(sb.toString());
    }

    private void c0_assertion_failure(String msg) {
        throw new RuntimeException(msg);
    }

    private static boolean val_equal(c0_value a, c0_value b) {
        return a.kind == b.kind && a.val == b.val;
    }

    private final ArrayList<FileHandle> allFiles = new ArrayList<>();
    private static final int fileHandlePointerMod = 0x46696C65;

    private final class FileHandle {

        private final BufferedReader br;
        private String nextLine;

        FileHandle(String path) throws IOException {
            this.br = new BufferedReader(new FileReader(path));
            this.nextLine = br.readLine();
        }

        boolean isEOF() {
            return nextLine == null;
        }

        String readLine() {
            if (nextLine == null) {
                c0_assertion_failure("Attempted to read past end of file");
            }
            String thisLine = nextLine;
            try {
                nextLine = br.readLine();
            } catch (IOException ex) {
                nextLine = null;
            }
            return thisLine;
        }
    }

    private String readStringFromHeap(int strAddr) {
        if (strAddr == Heap.NULL) {
            return "";
        }
        StringBuilder str = new StringBuilder();
        byte b = heap.read(strAddr, 1)[0];
        for (int i = 1; b != 0; i++) {
            str.append((char) b);
            b = heap.read(strAddr + i, 1)[0];
        }
        return str.toString();
    }

    private int writeStringToHeap(String str) {
        int len = str.length();
        int strAddr = heap.allocate(len + 1);
        byte[] strBytes = new byte[len + 1];
        strBytes[len] = 0;
        for (int i = 0; i < len; i++) {
            strBytes[i] = (byte) str.charAt(i);
        }
        heap.write(strAddr, strBytes);
        return strAddr;
    }

    private c0_value invokeNative(int nativeID, c0_value... args) {
        assert args != null;
        switch (nativeID) {
            /* 15411 */
            //<editor-fold desc="15411">
            case 0: //fadd
            {
                assert args.length == 2;
                assert args[0].kind == C0_INTEGER && args[1].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                float f2 = Float.intBitsToFloat(val2int(args[1]));
                return int2val(Float.floatToIntBits(f1 + f2));
            }
            case 1: //fdiv
            {
                assert args.length == 2;
                assert args[0].kind == C0_INTEGER && args[1].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                float f2 = Float.intBitsToFloat(val2int(args[1]));
                return int2val(Float.floatToIntBits(f1 / f2));
            }
            case 2: //fless
            {
                assert args.length == 2;
                assert args[0].kind == C0_INTEGER && args[1].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                float f2 = Float.intBitsToFloat(val2int(args[1]));
                if (f1 < f2) {
                    return int2val(1);
                } else {
                    return int2val(0);
                }
            }
            case 3: //fmul
            {
                assert args.length == 2;
                assert args[0].kind == C0_INTEGER && args[1].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                float f2 = Float.intBitsToFloat(val2int(args[1]));
                return int2val(Float.floatToIntBits(f1 * f2));
            }
            case 4: //fsub
            {
                assert args.length == 2;
                assert args[0].kind == C0_INTEGER && args[1].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                float f2 = Float.intBitsToFloat(val2int(args[1]));
                return int2val(Float.floatToIntBits(f1 - f2));
            }
            case 5: //ftoi
            {
                assert args.length == 1;
                assert args[0].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                return int2val((int) f1);
            }
            case 6: //itof
            {
                assert args.length == 1;
                assert args[0].kind == C0_INTEGER;
                int i = val2int(args[0]);
                return int2val(Float.floatToIntBits(i));
            }
            case 7: //print_fpt
            {
                assert args.length == 1;
                assert args[0].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                autoGrader.println(f1);
                return int2val(0);
            }
            case 8: //print_hex
            {
                assert args.length == 1;
                assert args[0].kind == C0_INTEGER;
                int i = val2int(args[0]);
                autoGrader.println(Integer.toHexString(i));
                return int2val(0);
            }
            case 9: //print_int
            {
                assert args.length == 1;
                assert args[0].kind == C0_INTEGER;
                float f1 = Float.intBitsToFloat(val2int(args[0]));
                autoGrader.println(f1);
                return int2val(0);
            }
            //</editor-fold>
            /* args */
            //<editor-fold desc="args">
            case 10: //args_flag
            case 11: //args_int
            case 12: //args_parse
            case 13: //args_string
            {
                throw new UnsupportedOperationException("C0 library <args> not supported yet");
            }
            //</editor-fold>
            /* conio */
            //<editor-fold desc="conio">
            case 14: { //eof
                throw new UnsupportedOperationException("C0 library function eof() in library <conio> not supported yet");
            }
            case 15: //flush
            {
                assert args.length == 0;
                System.out.flush();
                return int2val(0);
            }
            case 16: //print
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int start = val2ptr(args[0]);
                byte b = heap.read(start, 1)[0];
                for (int i = 0; b != 0; i++) {
                    System.out.print((char) b);
                    b = heap.read(start + i, 1)[0];
                }
                return int2val(0);
            }
            case 17: //printbool
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                if (val2int(args[0]) == 0) {
                    System.out.print("false");
                } else {
                    System.out.print("true");
                }
                return int2val(0);
            }
            case 18: //printchar
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                System.out.print((char) (val2int(args[0])) & 0x7F);
                return int2val(0);
            }
            case 19: //printint
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                System.out.print(val2int(args[0]));
                return int2val(0);
            }
            case 20: //println
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int start = val2ptr(args[0]);
                byte b = heap.read(start, 1)[0];
                for (int i = 0; b != 0; i++) {
                    System.out.print((char) b);
                    b = heap.read(start + i, 1)[0];
                }
                System.out.println();
                return int2val(0);
            }
            case 21: //readline
            {
                assert args.length == 0;
                BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
                String input;
                try {
                    input = br.readLine();
                } catch (IOException ex) {
                    input = "";
                }
                int startAddr = heap.allocate(input.length() + 1);
                for (int i = 0; i < input.length(); i++) {
                    heap.write(startAddr + i, (byte) input.charAt(i));
                }
                heap.write(startAddr + input.length(), (byte) 0);
                return ptr2val(startAddr);
            }
            //</editor-fold>
            /* curses */
            //<editor-fold desc="curses">
            case 22: //c_addch
            case 23: //c_cbreak
            case 24: //c_curs_set
            case 25: //c_delch
            case 26: //c_endwin
            case 27: //c_erase
            case 28: //c_getch
            case 29: //c_initscr
            case 30: //c_keypad
            case 31: //c_move
            case 32: //c_noecho
            case 33: //c_refresh
            case 34: //c_subwin
            case 35: //c_waddch
            case 36: //c_addstr
            case 37: //c_wclear
            case 38: //c_werase
            case 39: //c_wmove
            case 40: //c_wrefresh
            case 41: //c_wstandend
            case 42: //c_wstandout
            case 43: //cc_getbegx
            case 44: //cc_getbegy
            case 45: //cc_getmaxx
            case 46: //cc_getmaxy
            case 47: //cc_getx
            case 48: //cc_gety
            case 49: //cc_highlight
            case 50: //cc_key_is_backspace
            case 51: //cc_key_is_down
            case 52: //cc_key_is_enter
            case 53: //cc_key_is_left
            case 54: //cc_key_is_right
            case 55: //cc_key_is_up
            case 56: //cc_wboldoff
            case 57: //cc_wboldon
            case 58: //cc_wdimoff
            case 59: //cc_wdimon
            case 60: //cc_wreverseoff
            case 61: //cc_wreverseon
            case 62: //cc_wunderoff
            case 63: //cc_wunderon
            {
                throw new UnsupportedOperationException("Library <curses> not supported yet");
            }
            //</editor-fold>
            /* file */
            //<editor-fold desc="file">
            case 64: //file_close
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int handleIndex = heap.readInt(val2ptr(args[0])) - fileHandlePointerMod;
                FileHandle temp = allFiles.set(handleIndex, null);
                if (temp == null) {
                    c0_assertion_failure("Attempted to close already closed file");
                }
                return int2val(0);
            }
            case 65: //file_closed
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int handleIndex = heap.readInt(val2ptr(args[0])) - fileHandlePointerMod;
                if (allFiles.get(handleIndex) == null) {
                    return int2val(1);
                } else {
                    return int2val(0);
                }
            }
            case 66: //file_eof
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int handleIndex = heap.readInt(val2ptr(args[0])) - fileHandlePointerMod;
                FileHandle fh = allFiles.get(handleIndex);
                if (fh == null) {
                    c0_assertion_failure("Attempted to access closed file");
                } else {
                    if (fh.isEOF()) {
                        return int2val(1);
                    } else {
                        return int2val(0);
                    }
                }
            }
            case 67: //file_read
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                try {
                    int pathAddr = val2ptr(args[0]);
                    String path = readStringFromHeap(pathAddr);
                    FileHandle fh = new FileHandle(path);
                    int indexAddr = heap.allocate(4);
                    heap.writeInt(indexAddr, fileHandlePointerMod + allFiles.size());
                    allFiles.add(fh);
                    return ptr2val(indexAddr);
                } catch (IOException ioe) {
                    return ptr2val(Heap.NULL);
                }
            }
            case 68: //file_readline
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int indexAddr = val2ptr(args[0]);
                int handleIndex = heap.readInt(indexAddr) - fileHandlePointerMod;
                String line = allFiles.get(handleIndex).readLine();
                int strAddr = writeStringToHeap(line);
                return ptr2val(strAddr);
            }
            //</editor-fold>
            /* img */
            //<editor-fold desc="img">
            case 69: //image_clone
            case 70: //image_create
            case 71: //image_data
            case 72: //image_height
            case 73: //image_load
            case 74: //image_save
            case 75: //image_subimage
            case 76: //image_width
            {
                throw new UnsupportedOperationException("Library <img> not supported yet");
            }
            //</editor-fold>
            /* parse */
            //<editor-fold desc="parse">
            case 77: //bool int_tokens(string, int)
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_INTEGER;
                int base = val2int(args[1]);
                assert 2 <= base && base <= 36;
                int strStart = val2ptr(args[0]);
                //convert string in heap to a String object
                StringBuilder sb = new StringBuilder();
                byte b = heap.read(strStart, 1)[0];
                for (int i = 1; b != 0; i++) {
                    sb.append((char) b);
                    b = heap.read(strStart + i, 1)[0];
                }
                //let StringTokenizer do the work for us
                StringTokenizer st = new StringTokenizer(sb.toString());
                while (st.hasMoreTokens()) {
                    try {
                        //if this succeeds, the token was a valid integer
                        Integer.parseInt(st.nextToken(), base);
                    } catch (NumberFormatException nfe) {
                        return int2val(0);
                    }
                }
                return int2val(1);
            }
            case 78: //num_tokens
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int strStart = val2ptr(args[0]);
                StringBuilder sb = new StringBuilder();
                byte b = heap.read(strStart, 1)[0];
                for (int i = 1; b != 0; i++) {
                    sb.append((char) b);
                    b = heap.read(strStart + i, 1)[0];
                }
                StringTokenizer st = new StringTokenizer(sb.toString());
                return int2val(st.countTokens());
            }
            case 79: //parse_bool
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int strStart = val2ptr(args[0]);
                StringBuilder sb = new StringBuilder();
                byte b = heap.read(strStart, 1)[0];
                for (int i = 1; b != 0; i++) {
                    sb.append((char) b);
                    b = heap.read(strStart + i, 1)[0];
                }
                String str = sb.toString();
                switch (str) {
                    case "true": {
                        int temp = heap.allocate(4);
                        heap.writeInt(temp, 1);
                        return ptr2val(temp);
                    }
                    case "false": {
                        int temp = heap.allocate(4);
                        heap.writeInt(temp, 0);
                        return ptr2val(temp);
                    }
                    default:
                        return ptr2val(Heap.NULL);
                }
            }
            case 80: //parse_int
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_INTEGER;
                int base = val2int(args[1]);
                assert 2 <= base && base <= 36;
                int strStart = val2ptr(args[0]);
                StringBuilder sb = new StringBuilder();
                byte b = heap.read(strStart, 1)[0];
                for (int i = 1; b != 0; i++) {
                    sb.append((char) b);
                    b = heap.read(strStart + i, 1)[0];
                }
                try {
                    int val = Integer.parseInt(sb.toString(), base);
                    int valAddr = heap.allocate(4);
                    heap.writeInt(valAddr, val);
                    return ptr2val(valAddr);
                } catch (NumberFormatException nfe) {
                    return ptr2val(Heap.NULL);
                }
            }
            case 81: //parse_ints
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_INTEGER;
                int base = val2int(args[1]);
                assert 2 <= base && base <= 36;
                int strStart = val2ptr(args[0]);
                StringBuilder sb = new StringBuilder();
                byte b = heap.read(strStart, 1)[0];
                for (int i = 1; b != 0; i++) {
                    sb.append((char) b);
                    b = heap.read(strStart + i, 1)[0];
                }
                StringTokenizer st = new StringTokenizer(sb.toString());
                int numInts = st.countTokens();
                int[] vals = new int[numInts];
                for (int i = 0; i < numInts; i++) {
                    try {
                        vals[i] = Integer.parseInt(st.nextToken(), base);
                    } catch (NumberFormatException nfe) {
                        assert false;
                    }
                }
                int arrAddr = heap.allocate(12);
                heap.writeInt(arrAddr, 4);
                heap.writeInt(arrAddr + 4, numInts);
                int valsAddr = heap.allocate(4 * numInts);
                heap.writeInt(arrAddr + 8, valsAddr);
                for (int i = 0; i < numInts; i++) {
                    heap.writeInt(valsAddr + 4 * i, vals[i]);
                }
                return ptr2val(arrAddr);
            }
            case 82: //parse_tokens
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int strStart = val2ptr(args[0]);
                StringBuilder sb = new StringBuilder();
                byte b = heap.read(strStart, 1)[0];
                for (int i = 1; b != 0; i++) {
                    sb.append((char) b);
                    b = heap.read(strStart + i, 1)[0];
                }
                StringTokenizer st = new StringTokenizer(sb.toString());
                String[] tokens = new String[st.countTokens()];
                for (int i = 0; i < tokens.length; i++) {
                    tokens[i] = st.nextToken();
                }
                int arrAddr = heap.allocate(12);
                heap.writeInt(arrAddr, 1);
                heap.writeInt(arrAddr + 4, tokens.length);
                int valsAddr = heap.allocate(tokens.length * 4);
                heap.writeInt(arrAddr + 8, valsAddr);
                for (int i = 0; i < tokens.length; i++) {
                    String temp = tokens[i];
                    int tempAddr = heap.allocate(temp.length() + 1);
                    for (int j = 0; j < temp.length(); j++) {
                        heap.write(tempAddr + j, (byte) temp.charAt(j));
                    }
                    heap.write(tempAddr + temp.length(), (byte) 0);
                    heap.writeInt(valsAddr + 4 * i, tempAddr);
                }
                return ptr2val(arrAddr);
            }
            //</editor-fold>
            /* string */
            //<editor-fold desc="string">
            case 83: //char_chr
            case 84: //char_ord
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                return int2val(val2int(args[0]) & 0x7F);
            }
            case 85: //string_charat
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_INTEGER;
                String str = readStringFromHeap(val2ptr(args[0]));
                int index = val2int(args[1]);
                if (index < 0) {
                    c0_assertion_failure("index cannot be negative");
                }
                if (index >= str.length()) {
                    c0_assertion_failure("index is not less than string length");
                }
                char ch = str.charAt(index);
                assert ch >= 0 && ch < 127;
                return int2val(((byte) ch & 0x7F));
            }
            case 86: //string_compare
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_POINTER;
                String s1 = readStringFromHeap(val2ptr(args[0]));
                String s2 = readStringFromHeap(val2ptr(args[1]));
                return int2val((int) Math.signum(s1.compareTo(s2)));
            }
            case 87: //string_equal
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_POINTER;
                String s1 = readStringFromHeap(val2ptr(args[0]));
                String s2 = readStringFromHeap(val2ptr(args[1]));
                return int2val(s1.equals(s2) ? 1 : 0);
            }
            case 88: //string_from_chararray
            {
                assert args.length == 1;
                assert args[0].kind == C0_POINTER;
                int arrAddr = val2ptr(args[0]);
                assert heap.readInt(arrAddr) == 1;
                int valsAddr = heap.readInt(arrAddr + 8);
                return ptr2val(writeStringToHeap(readStringFromHeap(valsAddr)));
            }
            case 89: //string_from_bool
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                boolean value = (val2int(args[0]) != 0);
                return ptr2val(writeStringToHeap(String.valueOf(value)));
            }
            case 90: //string_from_char
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                int strAddr = heap.allocate(2);
                heap.write(strAddr, (byte) (val2int(args[0]) & 0x7F));
                heap.write(strAddr + 1, (byte) 0);
                return ptr2val(strAddr);
            }
            case 91: //string_fromint
            {
                assert args.length == 1 && args[0].kind == C0_INTEGER;
                int val = val2int(args[0]);
                String str = Integer.toString(val);
                int strAddr = heap.allocate(str.length() + 1);
                for (int i = 0; i < str.length(); i++) {
                    heap.write(strAddr + i, (byte) str.charAt(i));
                }
                heap.write(strAddr + str.length(), (byte) 0);
                return ptr2val(strAddr);
            }
            case 92: //string_join
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_POINTER;
                String s1 = readStringFromHeap(val2ptr(args[0]));
                String s2 = readStringFromHeap(val2ptr(args[1]));
                return ptr2val(writeStringToHeap(s1 + s2));
            }
            case 93: //string_length
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                return int2val(readStringFromHeap(val2ptr(args[0])).length());
            }
            case 94: //string_sub
            {
                assert args.length == 3 && args[0].kind == C0_POINTER;
                assert args[1].kind == C0_INTEGER && args[2].kind == C0_INTEGER;
                int strAddr = val2ptr(args[0]);
                int start = val2int(args[1]), end = val2int(args[2]);
                String str = readStringFromHeap(strAddr);
                if (!(0 <= start && start <= end && end <= str.length())) {
                    c0_assertion_failure("start and end values not within valid range");
                }
                return ptr2val(writeStringToHeap(str.substring(start, end)));
            }
            case 95: //string_terminated
            {
                assert args.length == 2;
                assert args[0].kind == C0_POINTER && args[1].kind == C0_INTEGER;
                int arrAddr = val2ptr(args[0]);
                int maxLen = val2int(args[1]);
                assert heap.readInt(arrAddr) == 1;
                int numElems = heap.readInt(arrAddr + 4);
                if (maxLen < 0 || maxLen >= numElems) {
                    c0_assertion_failure("int argument is not within valid range");
                }
                int dataAddr = heap.readInt(arrAddr + 8);
                byte[] arr = heap.read(dataAddr, numElems);
                assert maxLen <= numElems;
                for (int i = 0; i < maxLen; i++) {
                    if (arr[i] == 0) {
                        return int2val(1);
                    }
                }
                return int2val(0);
            }
            case 96: //string_to_chararray
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                int strAddr = val2ptr(args[0]);
                if (strAddr != Heap.NULL) {
                    int strLen = 0;
                    while (heap.read(strAddr + strLen, 1)[0] != 0) {
                        strLen++;
                    }
                    int arrAddr = heap.allocate(12);
                    heap.writeInt(arrAddr, 1);
                    heap.writeInt(arrAddr + 4, strLen);
                    int dataAddr = heap.allocate(strLen + 1);
                    heap.writeInt(arrAddr + 8, dataAddr);
                    heap.write(dataAddr, heap.read(strAddr, strLen + 1));
                    return ptr2val(arrAddr);
                } else {
                    int arrAddr = heap.allocate(12);
                    heap.writeInt(arrAddr, 1);
                    heap.writeInt(arrAddr + 4, 0);
                    heap.writeInt(arrAddr + 8, Heap.NULL);
                    return ptr2val(arrAddr);
                }
            }
            case 97: //string_tolower
            {
                assert args.length == 1 && args[0].kind == C0_POINTER;
                String str = readStringFromHeap(val2ptr(args[0]));
                return ptr2val(writeStringToHeap(str.toLowerCase()));
            }
            //</editor-fold>
        }
        throw new IllegalArgumentException("Invalid native ID: " + nativeID);
    }

    private static final boolean PRINT_DEBUG = false;

    /**
     * Runs the program held by this virtual machine instance.
     *
     * @return the value returned by the {@code int main()} function of this
     * VM's stored program. In most cases, this value should be printed.
     */
    private int execute() {
        byte[] P = functionPool[0].code;
        int pc = 0;
        Deque<c0_value> S = new LinkedList<>();
        c0_value[] V = new c0_value[functionPool[0].numVars];
        Deque<stackFrame> callStack = new LinkedList<>();
        int totalExecuted = 0;
        while (true) {
            byte instruction = P[pc];
//            if (totalExecuted == 1181) {
//                System.out.println();
//            }
            if (PRINT_DEBUG) {
                System.err.println("Opcode: " + Integer.toHexString(instruction & 0xFF).toUpperCase());
                System.err.println("Stack size: " + S.size());
                System.err.println("Call stack size: " + callStack.size());
                System.err.println("Program counter: " + pc);
                System.err.println("Total instructions executed: " + totalExecuted++);
            }
            switch (instruction) {
                case POP: {
                    pc++;
                    S.pop();
                    break;
                }

                case DUP: {
                    pc++;
                    c0_value v = S.pop();
                    S.push(v);
                    S.push(v);
                    break;
                }

                case SWAP: {
                    pc++;
                    c0_value v1 = S.pop();
                    c0_value v2 = S.pop();
                    S.push(v1);
                    S.push(v2);
                    break;
                }

                case RETURN: {
                    if (callStack.isEmpty()) {
                        assert (callStack.isEmpty());
                        int retval = val2int(S.pop());
                        assert (S.isEmpty());
                        return retval;
                    } else {
                        c0_value retval = S.pop();
                        stackFrame prev = callStack.pop();
                        S = prev.S;
                        V = prev.V;
                        P = prev.P;
                        pc = prev.pc;
                        S.push(retval);
                        if (PRINT_DEBUG) {
                            System.err.println("returning from function");
                        }
                    }
                    break;
                }

                /* Arithmetic and Logical operations */
                case IADD: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    S.push(int2val(x + y));
                    break;
                }
                case ISUB: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    S.push(int2val(x - y));
                    break;
                }
                case IMUL: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    S.push(int2val(x * y));
                    break;
                }
                case IDIV: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    if (y == 0) {
                        c0_arith_error("ArithmeticException: Integer division by zero");
                    } else if ((x == 0x80000000) && (y == -1)) {
                        c0_arith_error("ArithmeticException: Division of int_min by -1");
                    }
                    S.push(int2val(x / y));
                    break;
                }
                case IREM: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    if (y == 0) {
                        c0_arith_error("ArithmeticException: Modulo by zero");
                    } else if ((x == 0x80000000) && (y == -1)) {
                        c0_arith_error("ArithmeticException: Modulo of int_min by -1");
                    }
                    S.push(int2val(x % y));
                    break;
                }
                case IAND: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    S.push(int2val(x & y));
                    break;
                }
                case IOR: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    S.push(int2val(x | y));
                    break;
                }
                case IXOR: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    S.push(int2val(x ^ y));
                    break;
                }
                case ISHL: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    if (!(0 <= y && y <= 31)) {
                        c0_arith_error("ArithmeticException: Illegal bitshift");
                    }
                    S.push(int2val(x << y));
                    break;
                }
                case ISHR: {
                    pc++;
                    int y = val2int(S.pop());
                    int x = val2int(S.pop());
                    if (!(0 <= y && y <= 31)) {
                        c0_arith_error("ArithmeticException: Illegal bitshift");
                    }
                    S.push(int2val(x >> y));
                    break;
                }

                /* Pushing constants */
                case BIPUSH: {
                    pc++;
                    int x = P[pc++];
                    S.push(int2val(x));
                    break;
                }
                case ILDC: {
                    pc++;
                    int index = (((((int) P[pc++]) & 0xFF) << 8)
                            + (((int) P[pc++]) & 0xFF));
                    S.push(int2val(intPool[index]));
                    break;
                }
                case ALDC: {
                    pc++;
                    int index = (((((int) P[pc++]) & 0xFF) << 8)
                            + (((int) P[pc++]) & 0xFF));
                    S.push(ptr2val(index));
                    break;
                }

                case ACONST_NULL: {
                    pc++;
                    S.push(ptr2val(Heap.NULL));
                    break;
                }


                /* Operations on local variables */
                case VLOAD: {
                    pc++;
                    S.push(V[P[pc++]]);
                    break;
                }

                case VSTORE: {
                    pc++;
                    V[P[pc++]] = S.pop();
                    break;
                }

                /* Control flow operations */
                case NOP: {
                    pc++;
                    break;
                }
                case IF_CMPEQ: {
                    c0_value y = S.pop();
                    c0_value x = S.pop();
                    int jump = ((((short) P[pc + 1]) & 0xFF) << 8)
                            | (((short) P[pc + 2]) & 0xFF);
                    if (val_equal(x, y)) {
                        pc += jump;
                    } else {
                        pc += 3;
                    }
                    break;
                }
                case IF_CMPNE: {
                    c0_value y = S.pop();
                    c0_value x = S.pop();
                    int jump = ((((short) P[pc + 1]) & 0xFF) << 8)
                            | (((short) P[pc + 2]) & 0xFF);
                    if (!val_equal(x, y)) {
                        pc += jump;
                    } else {
                        pc += 3;
                    }
                    break;
                }
                case IF_ICMPLT: {
                    c0_value y = S.pop();
                    c0_value x = S.pop();
                    int jump = ((((short) P[pc + 1]) & 0xFF) << 8)
                            | (((short) P[pc + 2]) & 0xFF);
                    assert (x.kind == C0_INTEGER);
                    assert (y.kind == C0_INTEGER);
                    if (val2int(x) < val2int(y)) {
                        pc += jump;
                    } else {
                        pc += 3;
                    }
                    break;
                }
                case IF_ICMPGE: {
                    c0_value y = S.pop();
                    c0_value x = S.pop();
                    int jump = ((((short) P[pc + 1]) & 0xFF) << 8)
                            | (((short) P[pc + 2]) & 0xFF);
                    assert (x.kind == C0_INTEGER);
                    assert (y.kind == C0_INTEGER);
                    if (val2int(x) >= val2int(y)) {
                        pc += jump;
                    } else {
                        pc += 3;
                    }
                    break;
                }
                case IF_ICMPGT: {
                    c0_value y = S.pop();
                    c0_value x = S.pop();
                    int jump = ((((short) P[pc + 1]) & 0xFF) << 8)
                            | (((short) P[pc + 2]) & 0xFF);
                    assert (x.kind == C0_INTEGER);
                    assert (y.kind == C0_INTEGER);
                    if (val2int(x) > val2int(y)) {
                        pc += jump;
                    } else {
                        pc += 3;
                    }
                    break;
                }
                case IF_ICMPLE: {
                    c0_value y = S.pop();
                    c0_value x = S.pop();
                    int jump = ((((short) P[pc + 1]) & 0xFF) << 8)
                            | (((short) P[pc + 2]) & 0xFF);
                    assert (x.kind == C0_INTEGER);
                    assert (y.kind == C0_INTEGER);
                    if (val2int(x) <= val2int(y)) {
                        pc += jump;
                    } else {
                        pc += 3;
                    }
                    break;
                }
                case GOTO: {
                    pc += (short) (((P[pc + 1] & 0xFF) << 8) | (P[pc + 2] & 0xFF));
                    break;
                }

                case ATHROW: {
                    pc++;
                    c0_user_error(val2ptr(S.pop()));
                    break;
                }
                case ASSERT: {
                    pc++;
                    c0_value a = S.pop();
                    c0_value x = S.pop();
                    assert (a.kind == C0_POINTER);
                    assert (x.kind == C0_INTEGER);
                    if (val2int(x) == 0) {
                        c0_assertion_failure(val2ptr(a));
                    }
                    break;
                }

                /* Function call operations: */
                case INVOKESTATIC: {
                    pc++;
                    //prepare function arguments for invoked function
                    int functionIndex = ((P[pc++] << 8) + (P[pc++]));
                    if (PRINT_DEBUG) {
                        System.err.println("Invoked function " + functionIndex);
                    }
                    Function called = functionPool[functionIndex];
                    int numArgs = called.numArgs;
                    c0_value[] args = new c0_value[numArgs];
                    for (int i = numArgs - 1; i >= 0; i--) {
                        args[i] = S.pop();
                    }
                    //store current frame
                    stackFrame current = new stackFrame(P, pc, S, V);
                    callStack.push(current);
                    //set current frame to be the beginning of the invoked function
                    P = called.code;
                    S = new LinkedList<>();
                    V = new c0_value[called.numVars];
                    System.arraycopy(args, 0, V, 0, numArgs);
                    pc = 0;
                    break;
                }
                case INVOKENATIVE: {
                    pc++;
                    int nativeIndex = (((int) P[pc++] << 8) + P[pc++]);
                    int functionIndex = this.nativeIDs[nativeIndex];
                    int numArgs = this.nativeArgCounts[nativeIndex];
                    c0_value[] args = new c0_value[numArgs];
                    for (int i = numArgs - 1; i >= 0; i--) {
                        args[i] = S.pop();
                    }
                    c0_value retVal = invokeNative(functionIndex, args);
                    S.push(retVal);
                    break;
                }

                /* Memory allocation operations: */
                case NEW: {
                    pc++;
                    int size = P[pc++];
                    int allocated = heap.allocate(size);
                    S.push(ptr2val(allocated));
                    break;
                }
                case NEWARRAY: {
                    pc++;
                    int s = P[pc++] & 0xFF; //value should be unsigned
                    c0_value temp = S.pop();
                    assert (temp.kind == C0_INTEGER);
                    int n = val2int(temp);
                    assert n >= 0;
                    int arr = heap.allocate(12);
                    heap.writeInt(arr, s);
                    heap.writeInt(arr + 4, n);
                    heap.writeInt(arr, heap.allocate(s * n));
                    S.push(ptr2val(arr));
                    break;
                }
                case ARRAYLENGTH: {
                    pc++;
                    c0_value arrPtr = S.pop();
                    assert (arrPtr.kind == C0_POINTER);
                    if (val2ptr(arrPtr) == Heap.NULL) {
                        S.push(int2val(0));
                    } else {
                        int arrAddr = val2ptr(arrPtr);
                        S.push(int2val(heap.readInt(arrAddr + 4)));
                    }
                    break;
                }

                /* Memory access operations: */
                case AADDF: {
                    pc++;
                    int f = P[pc++];
                    c0_value a = S.pop();
                    assert (a.kind == C0_POINTER);
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("NullPointerException");
                    }
                    S.push(ptr2val(f + val2ptr(a)));
                    break;
                }
                case AADDS: {
                    pc++;
                    c0_value i = S.pop();
                    c0_value a = S.pop();
                    assert (i.kind == C0_INTEGER);
                    assert (a.kind == C0_POINTER);
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("NullPointerException");
                    }
                    int arrAddr = val2ptr(a);
                    int index = val2int(i);
                    if (index < 0 || index >= heap.readInt(arrAddr + 4)) {
                        c0_memory_error("ArrayIndexOutOfBoundsException: " + index);
                    }
                    int newPtr = heap.readInt(arrAddr + 4) + heap.readInt(arrAddr) * index;
                    S.push(ptr2val(newPtr));
                    break;
                }
                case IMLOAD: {
                    pc++;
                    c0_value a = S.pop();
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("Attempted to dereference null pointer");
                    }
                    int ptrVal = heap.readInt(val2ptr(a));
                    S.push(int2val(ptrVal));
                    break;
                }
                case IMSTORE: {
                    pc++;
                    c0_value x = S.pop();
                    c0_value a = S.pop();
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("Attempted to dereference null pointer");
                    }
                    heap.writeInt(val2ptr(a), val2int(x));
                    break;
                }
                case AMLOAD: {
                    pc++;
                    c0_value a = S.pop();
                    assert (a.kind == C0_POINTER);
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("Attempted to dereference null pointer");
                    }
                    int ptrVal = heap.readInt(val2ptr(a));
                    S.push(ptr2val(ptrVal));
                    break;
                }
                case AMSTORE: {
                    pc++;
                    c0_value b = S.pop();
                    c0_value a = S.pop();
                    assert (b.kind == C0_POINTER);
                    assert (a.kind == C0_POINTER);
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("Attempted to dereference null pointer");
                    }
                    heap.writeInt(val2ptr(a), val2ptr(b));
                    break;
                }
                case CMLOAD: {
                    pc++;
                    c0_value a = S.pop();
                    assert (a.kind == C0_POINTER);
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("Attempted to dereference null pointer");
                    }
                    int ptrVal = heap.read(val2ptr(a), 1)[0] & 0x7F;
                    S.push(int2val(ptrVal));
                    break;
                }
                case CMSTORE: {
                    pc++;
                    c0_value x = S.pop();
                    c0_value a = S.pop();
                    assert (x.kind == C0_INTEGER);
                    assert (a.kind == C0_POINTER);
                    if (val2ptr(a) == Heap.NULL) {
                        c0_memory_error("Attempted to dereference null pointer");
                    }
                    heap.write(val2ptr(a), (byte) (val2int(x) & 0x7F));
                    break;
                }
                default: {
                    throw new RuntimeException("invalid opcode: 0x" + Integer.toHexString(P[pc]));

                }
            }
            if (PRINT_DEBUG) {
                System.err.println();
            }
        }
    }

    public static int run(String path) throws IOException {
        return run(new File(path));
    }

    public static int run(File f) throws IOException {
        C0VM vm = new C0VM(f);
        return vm.execute();
    }

}
