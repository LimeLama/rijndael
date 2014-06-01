using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Security.Cryptography;

namespace rijndael
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
        }

        class gf256
        {
            private byte[] inv_table = new byte[256];

            public gf256()
            {
                for (byte i = 0; ; i++)
                {
                    for (byte j = 0; ; j++)
                    {
                        if (mul(j, i) == 1) { inv_table[i] = j; }
                        if (j == 0xff)
                        {
                            break;
                        }
                    }
                    if (i == 0xff)
                    {
                        break;
                    }
                }

            }

            public byte inv(byte a)
            {
                return inv_table[a];
            }

            public byte xtime(byte p)
            {
                byte highbit = (byte)(p & 0x80);
                byte r=(byte)((p << 1) & 0xff);
                return highbit == 0 ? (byte)r : (byte)(r ^ 0x1b);
            }

            public byte mul(byte a,byte b)
            {
                byte ret=0;
                //int p = b1;

                for (byte i = 0; i <= 7;i++)
                {
                    if ((b & 1) == 1)
                    {
                        ret ^= a;
                    }
                    a = xtime(a);
                    b >>= 1;
                }
                
                return ret;
            }
        }

        

        public class rijndael
        {
            private gf256 gf=new gf256();
            private byte[] SBox=new byte[256];
            private byte[] InvSBox = new byte[256];
            private string keyword;
            private byte[] hashKey;
            private int Nb,Nk,Nr;
            private byte[][][] w;
            private byte[][] cipherKey;
            private byte[][] Rcon;
            private int keySize;
            private byte[][] mixMatrix;

            protected rijndael(string password,int type)
            {
                MD5 md5 = MD5.Create();
                keyword = password;
                keySize = type;
                if (keySize == 128)
                {
                    Nb = 4;
                    Nk = 4;
                    Nr = 10;
                    hashKey = md5.ComputeHash(Encoding.UTF8.GetBytes(keyword));
                }
                if (keySize == 192)
                {
                    Nb = 6;
                    Nk = 4;
                    Nr = 12;
                }
                if (keySize == 256)
                {
                    Nb = 8;
                    Nk = 4;
                    Nr = 14;
                }
                SBox_init();
                InvSBox_init();
                
                
                //w = new byte[Nr, 4, Nb];
                cipherKey_init();
                Rcon_init();
                mix_init();
                keyexpansion();
                cipherBlock(new byte[32]);
            }

            private byte[] cipherBlock(byte[] plainText)
            {
                byte[] cipherText={0,0,0,0};
                byte[][] cipherMatrix;

                cipherMatrix = new byte[Nb][];
                for (int i = 0; i < Nk; i++)
                {
                    cipherMatrix[i] = new byte[Nb];
                    for (int j = 0; j < Nb; j++)
                    {
                        cipherMatrix[i][j] = plainText[Nk * j + i];
                    }
                }

                AddRoundKey(0, cipherMatrix);

                cipherMatrix[0] = new byte[4] { 0x19, 0x3d, 0xe3, 0xbe };
                cipherMatrix[1] = new byte[4] { 0xa0, 0xf4, 0xe2, 0x2b };
                cipherMatrix[2] = new byte[4] { 0x9a, 0xc6, 0x8d, 0x2a };
                cipherMatrix[3] = new byte[4] { 0xe9, 0xf8, 0x48, 0x08 };

                for (int i = 1; i < Nr; i++)
                {
                    SubBytes(cipherMatrix);
                    ShiftRows(cipherMatrix);
                    MixColumns(cipherMatrix);
                    AddRoundKey(i, cipherMatrix);
                }

                SubBytes(cipherMatrix);
                ShiftRows(cipherMatrix);
                AddRoundKey(10, cipherMatrix);

                return cipherText;
            }

            private void AddRoundKey(int index, byte[][] matrix)
            {
                //byte[][] result;
                //result = new byte[Nb][];

                for (int i=0; i<Nb; i++)
                {
                    //result[i] = new byte[Nb];
                    for (int j = 0; j < Nb; j++)
                    {
                        matrix[i][j] = (byte)(w[index][i][j] ^ matrix[i][j]);
                    }
                }

                //return result;
            }

            private void SubBytes(byte[][] matrix)
            {
                for (int i = 0; i < Nb; i++)
                {
                    for (int j = 0; j < Nb; j++)
                    {
                        matrix[i][j] = SBox[matrix[i][j]];
                    }
                }
            }

            private void ShiftRows(byte[][] matrix)
            {
                for (int i = 0; i < 4; i++)
                {
                    for (int j = i; j > 0; j--)
                    {

                        byte[] temp = rotWord(new byte[4]{matrix[0][i],matrix[1][i],matrix[2][i],matrix[3][i]});
                        matrix[0][i] = temp[0];
                        matrix[1][i] = temp[1];
                        matrix[2][i] = temp[2];
                        matrix[3][i] = temp[3];
                    }
                }
            }

            private void MixColumns(byte[][] matrix)
            {
                for(int i=0; i <4 ;i++)
                {
                    byte[] column = new byte[4];
                    for (int j = 0; j < 4; j++)
                    {
                        column[j]=0;
                        for (int k = 0; k < 4;  k++)
                        {
                            column[j] ^= gf.mul(matrix[i][k], mixMatrix[j][k]);
                        }
                    }
                    matrix[i] = column;
                }
            }



            private void Rcon_init()
            {
                byte r = 1;
                Rcon = new byte[Nr][];
                Rcon[0]=new byte[4]{r,0,0,0};
                for (int i = 1; i < Nr; i++)
                {
                    r = gf.xtime(r);
                    Rcon[i] = new byte[4] { r, 0, 0, 0 };
                }
            }

            private void cipherKey_init()
            {
                cipherKey = new byte[Nk][];
                for (int i = 0; i < Nk; i++)
                {
                    cipherKey[i] = new byte[Nb];
                    for (int j = 0; j < Nb; j++)
                    {
                        cipherKey[i][j]=hashKey[Nk*j+i];
                    }
                }
            }

            private void mix_init()
            {
                mixMatrix = new byte[4][];

                mixMatrix[0] = new byte[4] { 0x02, 0x03, 0x01, 0x01 };
                mixMatrix[1] = new byte[4] { 0x01, 0x02, 0x03, 0x01 };
                mixMatrix[2] = new byte[4] { 0x01, 0x01, 0x02, 0x03 };
                mixMatrix[3] = new byte[4] { 0x03, 0x01, 0x01, 0x02 };
            }

            private void keyexpansion()
            {
                w = new byte[Nr + 1][][];

                //cipherKey = new byte[4][]; 

                cipherKey[0] = new byte[4] { 0x2b, 0x7e, 0x15, 0x16 };
                cipherKey[1] = new byte[4] { 0x28, 0xae, 0xd2, 0xa6 };
                cipherKey[2] = new byte[4] { 0xab, 0xf7, 0x15, 0x88 };
                cipherKey[3] = new byte[4] { 0x09, 0xcf, 0x4f, 0x3c };

                w[0]=cipherKey;
                int k = 0;
                byte[] temp;
                for (int i = Nk; i < Nb * (Nr + 1); i++)
                {

                    if (i % Nk == 0)
                    {
                        k++;
                        //Array.Copy(w[k - 1][Nk - 1], temp, w.Length);
                        temp = w[k - 1][Nk - 1];
                        w[k] = new byte[Nk][];
                        temp = xorWord(subWord(rotWord(temp)), Rcon[k - 1]);
                    }
                    else
                    {
                        //Array.Copy(w[k][(i % Nk) - 1], temp, w.Length);
                        temp = w[k][(i % Nk) - 1];
                    }

                    if ((i % Nk == 4) && (Nk == 8))
                    {
                        //Array.Copy(w[k][3], temp, w.Length);
                        temp = w[k][3];
                        temp = subWord(temp);
                    }

                    w[k][i % Nk] = xorWord(temp, w[k - 1][i % Nk]);
                    Console.WriteLine("");
                }
            }

            private byte[] xorWord(byte[] w, byte[] r)
            {
                byte[] ret = new byte[w.Length];
                if(w.Length!=r.Length){Console.WriteLine("xorWord error: arrays of different size");}
                for (int i = 0; i < w.Length; i++)
                {
                    ret[i] = (byte)(w[i] ^ r[i]);
                }
                return ret;
            }

            private byte[] subWord(byte[] w)
            {
                byte[] ret = new byte[w.Length];
                for (int i = 0; i < w.Length; i++)
                {
                    ret[i] = SBox[w[i]];
                }
                return ret;
            }

            private byte[] rotWord(byte[] w)
            {
                byte[] ret = new byte[w.Length];
                byte k = w[0];
                for(int i=1;i<w.Length;i++)
                {
                    ret[i - 1] = w[i];
                }
                ret[w.Length - 1] = k;
                return ret;
            }

            private void SBox_init()
            {
                byte m = 0xf8;

                for (byte i = 0; ; i++)
                {
                    byte r = 0;
                    byte q = gf.inv(i);
                    for (byte j=0; j <= 7;j++)
                    {
                        r = (byte)((byte)(r << 1) | xorbits((byte)(q & m)));
                        m = (byte)((m >> 1) | ((m & 1) << 7));
                    }
                    SBox[i] = (byte)(r^0x63);
                    if (i == 0xff) { break; }
                }

            }

            private byte xorbits(byte n)
            {
                byte ret=0;

                for (int i = 0; i < 8; i++)
                {
                    ret ^= (byte)(n & 1);
                    n >>= 1;
                }

                return ret;
            }

            private void InvSBox_init()
            {
                for(byte i=0;;i++)
                {
                    InvSBox[SBox[i]] = i;
                    if (i == 0xff) { break; }
                }
            }
        }

        public class rijndael_128 : rijndael
        {
            public rijndael_128(string password)
                :base(password,128)
            {
                
            }
            
        }

        public class rijndael_192 : rijndael
        {
            public rijndael_192(string password)
                : base(password, 192)
            {

            }

        }

        public class rijndael_256 : rijndael
        {
            public rijndael_256(string password)
                : base(password, 256)
            {

            }

        }

        private void button1_Click(object sender, EventArgs e)
        {
            //gf256 gf=new gf256();            
            rijndael rind128 = new rijndael_128("123");
            //rijndael rind192 = new rijndael_192("123");
            //rijndael rind256 = new rijndael_256("123");
            //int[][] w=new int[][]
            //{
            //    new int[]{1,2,3,4},
            //    new int[]{5,6,7,8},
            //    new int[]{9,10,11,12}
            //};
            
        }
    }
}
