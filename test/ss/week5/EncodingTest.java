package ss.week5;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Hex;

/**
 * A simple class that experiments with the Hex encoding
 * of the Apache Commons Codec library.
 *
 */
public class EncodingTest {
    public static void main(String[] args) throws DecoderException {
        String input = "Hello Big World";

        System.out.println(Hex.encodeHexString(input.getBytes()));

        String hexString = "4d6f64756c652032";
        byte[] bytes = Hex.decodeHex(hexString.toCharArray());
        System.out.println(new String(bytes));
    }
}