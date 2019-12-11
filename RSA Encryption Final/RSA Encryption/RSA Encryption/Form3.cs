
using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Numerics;
using System.Drawing;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;

namespace RSA_Encryption
{
    public partial class Form3 : Form
    {
        private static string MessageAscii = "";
        private static string PublicKey;
        private static string PrivateKey = "";
        private static BigInteger MAX_VAL = BigInteger.Pow(2, 128);
        public static BigInteger KeyLenght;


        private static bool IsDigitsOnly(string str)
        {
            foreach (char c in str)
            {
                if (c < '0' || c > '9')
                    return false;
            }

            return true;
        }
        private static void PrepareVariables(string msg, string key)
        {
            int i = 0;
            string x;
            byte[] MessageSendInAscii = Encoding.ASCII.GetBytes(msg);
            MessageAscii = "1";
            foreach (byte b in MessageSendInAscii)
            {

                if (Math.Floor(Math.Log10(b) + 1) == 2)
                {
                    x = Convert.ToString(b);
                    x = x.PadLeft(3, '0');
                    //MessageSendInAscii[i++] = Convert.ToByte(x);
                    MessageAscii += x;
                    //Debug.WriteLine(MessageSendInAscii[i-1]);
                }
                else
                {
                    x = Convert.ToString(b);
                    MessageAscii += x;
                }

            }
            // Debug.WriteLine(MessageAscii);
            // MessageAscii = string.Join(" ", MessageSendInAscii);
            if (!IsDigitsOnly(key))
            {
                MessageBox.Show("Friend public key must be a number!");
                PublicKey = "";
            }
            else PublicKey = key;
            //MessageAscii = "1072105044032104111119032097114101032121111117063013010";
        }
        private static string AsciiToText(string asciiMessage)
        {
            int x = 0, i = 3;
            string TextMessage = "", temp = "";
            asciiMessage = asciiMessage.Substring(1, asciiMessage.Length - 1);
            int lenghtsize = asciiMessage.Length;
            while (i <= lenghtsize)
            {
                temp = new string(asciiMessage.Take(3).ToArray());
                asciiMessage = asciiMessage.Substring(3, asciiMessage.Length - 3);
                TextMessage += Char.ConvertFromUtf32(Convert.ToInt32(temp.TrimStart('0')));
                i += 3;
            }

            return TextMessage;

        }
        private void InitSize(object sender)
        {
            int width = 240, height = 250;
            this.MinimumSize = new Size(width, height);
            textBox3.ReadOnly = true;
            textBox3.BorderStyle = 0;
            textBox3.BackColor = this.BackColor;
            textBox3.TabStop = false;


        }
        private BigInteger RandomInteger(BigInteger bound)
        {
            var rng = new RNGCryptoServiceProvider();
            var buffer = (bound << 16).ToByteArray(); // << 16 adds two bytes

            var generatedValueBound = BigInteger.One << (buffer.Length * 8 - 1); //-1 accounts for the sign bit
            var validityBound = generatedValueBound - generatedValueBound % bound;

            while (true)
            {
                //random value in [0, 2^(buffer.Length * 8 - 1))
                rng.GetBytes(buffer);
                buffer[buffer.Length - 1] &= 0x7F; //force sign bit to positive
                var r = new BigInteger(buffer);
                if (r >= validityBound) continue;
                return r % bound;
            }
        }
        private BigInteger RandomInteger(int n)
        {
            var rng = new RNGCryptoServiceProvider();
            byte[] bytes = new byte[n / 8];

            rng.GetBytes(bytes);

            var msb = bytes[n / 8 - 1];
            var mask = 0;
            while (mask < msb)
                mask = (mask << 1) + 1;

            bytes[n - 1] &= Convert.ToByte(mask);
            BigInteger p = new BigInteger(bytes);
            return p;
        }
        private bool IsProbabilyPrime(BigInteger n, int k = 20)
        {
            bool result = false;
            if (n < 2)
                return false;
            if (n == 2)
                return true;
            if (n % 2 == 0)
                return false;
            if (n % 3 == 0)
                return false;
            if (n % 5 == 0)
                return false;
            BigInteger d = n - 1;
            BigInteger s = 0;
            while (d % 2 == 0)
            {
                d >>= 1;
                s = s + 1;
            }
            for (int i = 0; i < k; i++)
            {
                BigInteger a;
                do
                {
                    a = RandomInteger(n - 2);
                }
                while (a < 2 || a >= n - 2);


                if (BigInteger.ModPow(a, d, n) == 1) return true;
                for (int j = 0; j < s - 1; j++)
                {
                    if (BigInteger.ModPow(a, 2 * j * d, n) == n - 1)
                        return true;
                }
                result = false;
            }
            return result;
        }
        private BigInteger GeneratePrime(string upperBound)
        {
            if (upperBound != null)
            {
                BigInteger p = RandomInteger(BigInteger.Parse(upperBound));
                while (!IsProbabilyPrime(p, 20))
                {
                    p = RandomInteger(BigInteger.Parse(upperBound));
                }
                return p;
            }
            else
            {
                Debug.WriteLine("Upper Bound should not be NULL!");
                BigInteger p = 0; return p;
            }

        }
        private BigInteger EuclideanGCD(BigInteger A, BigInteger B)
        {
            if (B == 0)
                return A;
            if (A == 0)
                return B;
            if (A > B)
                return EuclideanGCD(B, A % B);
            else
                return EuclideanGCD(B % A, A);
        }
        private BigInteger[] Extended_GCD(BigInteger A, BigInteger B)
        {
            //found this algorithm on Stack Overflow
            BigInteger[] result = new BigInteger[3];
            bool reverse = false;
            if (A < B) // interchange
            {
                BigInteger temp = A;
                A = B;
                B = temp;
                reverse = true;
            }

            BigInteger r = B;
            BigInteger q = 0;
            BigInteger x0 = 1;
            BigInteger y0 = 0;
            BigInteger x1 = 0;
            BigInteger y1 = 1;
            BigInteger x = 0, y = 0;

            while (A % B != 0)
            {
                r = A % B;
                q = A / B;
                x = x0 - q * x1;
                y = y0 - q * y1;
                x0 = x1;
                y0 = y1;
                x1 = x;
                y1 = y;
                A = B;
                B = r;
            }
            result[0] = r;
            if (reverse)
            {
                result[1] = y;
                result[2] = x;
            }
            else
            {
                result[1] = x;
                result[2] = y;
            }
            return result;
        }
        private BigInteger GeneratePublicKey(BigInteger bound)
        {
            BigInteger temp = 0;
            while (EuclideanGCD(temp, bound) != 1)
                temp = GeneratePrime(bound.ToString());
            return temp;
        }
        private BigInteger GeneratePrivateKey(BigInteger Totient, BigInteger E)
        {

            BigInteger[] result = new BigInteger[3];
            result = Extended_GCD(Totient, E);
            if (result[2] < 0)
                result[2] = result[2] + Totient;
            return result[2];

        }
        private string EncryptMessage(string PlainMessage, BigInteger E, BigInteger N)
        {
            return BigInteger.ModPow(BigInteger.Parse(PlainMessage), E, N).ToString();
        }
        private string DecryptMessage(string EncryptedMessage, BigInteger D, BigInteger N)
        {
            return BigInteger.ModPow(BigInteger.Parse(EncryptedMessage), D, N).ToString();
        }

        public Form3()
        {
            BigInteger P = GeneratePrime(MAX_VAL.ToString()); //First prime
            BigInteger Q = GeneratePrime(MAX_VAL.ToString()); //Second prime
            BigInteger N = BigInteger.Multiply(P, Q); //modulus for both the public and private keys
            BigInteger Totient = BigInteger.Multiply(P - 1, Q - 1); // Carmichael's totient
            BigInteger E = GeneratePublicKey(65537); // For efficiency reasons; anything smaller than 65,537(2^16 + 1)
                                                     // E is used to encrypt with public key
            BigInteger D = GeneratePrivateKey(Totient, E); // D = private key
            KeyLenght = N;
            PrivateKey = D.ToString();
            //Debug.WriteLine(EncryptedMessage);
            InitializeComponent();
            InitSize(this);
            //textBox1.Text = AsciiToText(DecryptMessage(EncryptedMessage, D, N));
            textBox3.Text = E.ToString();
        }
        private void button3_Click_1(object sender, EventArgs e)
        {
            PrepareVariables(textBox1.Text, textBox2.Text);
            if (!(MessageAscii == "1" || PublicKey == ""))
            {
                //Debug.WriteLine(MessageAscii);
                string EncryptedMessage = EncryptMessage(MessageAscii, BigInteger.Parse(PublicKey), Form1.KeyLenght);
                textBox1.Text = EncryptedMessage;
                MessageAscii = "";
                PublicKey = "";
            }
            else
            {
                MessageBox.Show("No message or no public key to use!");

            }
        }
        private void button1_Click(object sender, EventArgs e)
        {
            if (textBox1.Text != "" && IsDigitsOnly(textBox1.Text))
            {
                string decryptMessage = DecryptMessage(textBox1.Text, BigInteger.Parse(PrivateKey), KeyLenght);
                textBox1.Text = AsciiToText(decryptMessage);
                MessageAscii = "";
                PublicKey = "";

            }
            else
            {
                MessageBox.Show("Nothing to decrypt");
                textBox1.Text = PrivateKey;
            }
        }
        private void Form3_Load(object sender, EventArgs e)
        {

        }
    }
}
