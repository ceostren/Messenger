/*
 *File: Program.cs
 * Program: Messenger
 * Author: Carl Ostrenga ceo8099@g.rit.edu
 * Description: Program which allows for web based public key encrypted secure messaging using
 * RSA encryption and Decryption 
 */

using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Net.Http;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Serialization;
using System.Threading.Tasks;
using static System.Text.Json.JsonSerializer;



namespace Messenger
{
    
    //Class to generate random primes 
    public static class PrimeGen
    {
        private static object myLock = 1;
        private static int numcount = 1;

        /*
         * Extension method with tests whether the BigInt it is called on is most likely prime with a variable level of
         * certainty
         * value: this, the big integer which the extension is called on
         * witnesses: the level of certainty for the prime value, defaults to 10
         *
         * return: true if most likely prime, false otherwise
         */
        static Boolean IsProbablyPrime(this BigInteger value, int witnesses = 10)
        {
            if (value <= 1) return false;

            if (witnesses <= 0) witnesses = 10;

            BigInteger d = value - 1;
            int s = 0;

            while (d % 2 == 0)
            {
                d /= 2;
                s += 1;
            }

            Byte[] bytes = new Byte[value.ToByteArray().LongLength];
            BigInteger a;

            for (int i = 0; i < witnesses; i++)
            {
                do
                {
                    var Gen = new Random();
                    Gen.NextBytes(bytes);
                    a = new BigInteger(bytes);
                } while (a < 2 || a >= value - 2);

                BigInteger x = BigInteger.ModPow(a, d, value);
                if (x == 1 || x == value - 1) continue;

                for (int r = 1; r < s; r++)
                {
                    x = BigInteger.ModPow(x, 2, value);
                    if (x == 1) return false;
                    if (x == value - 1) break;
                }

                if (x != value - 1) return false;
            }

            return true;
        }


        /*
         * generateFunction is the main function which generates the requested number of primes
         * utilizes a Parallel forloop to generate the requested number of bigInts randomly, then
         * regenerates the numbers until each finds a prime
         *
         * int bits: the number of bits long each prime number must be, must be a multiple of 8
         * int count: the number of prime numbers to generate
         *
         * returns: None prints the discovered prime numbers to the console
         */
        public static BigInteger generateFunction(int bits, int count)
        {
            BigInteger res = 0;
            var RNG = new RNGCryptoServiceProvider();
            Parallel.For(0, count, cur =>
            {
                Boolean prime = true;
                BigInteger x;

                do
                {
                    var byteArr = new byte[bits / 8];

                    RNG.GetBytes(byteArr);
                    byteArr[byteArr.Length - 1] &= (Byte) 0x7F;
                    x = new BigInteger(byteArr);

                    prime = x.IsProbablyPrime();
                } while (!prime);

                lock (myLock)
                {
                    res = x;
                    //Console.WriteLine("{0}: {1}\n", numcount, x);
                    numcount += 1;
                }

            });
            return res;
        }
        
    }
    
    static class Helper
    {
        //Extension method to generate sub arrays for parsing
        public static T[] SubArray<T>(this T[] data, BigInteger i, BigInteger len)
        {
            T[] result = new T[(int)len];
            Array.Copy(data,(int)i,result,0,(int)len);
            return result;
        }
    }
    
    
    //Primary class for messenger program
    class SecureMessenger
    {
        //Sub class for key holding json messages
        class KeyMsg
        {
            
            //property for email associated with the key
            public string email { get; set; }
            //property for key
            public string key { get; set; }

            
        }

        //Subclass to make a json object to hold message information
        class MessMsg
        {
            public string email { get; set; }
            public string content { get; set; }
        }

        //Subclass to hold the private key and associated emails
        class PrivKey
        {
            public string key { get; set; }
            public string[] emails { get; set; }

            //Function to add a new email that is associated with the private key
            public void addEmail(string email)
            {
                string[] nEmails = (string[]) emails.Clone();
                Array.Resize(ref nEmails, nEmails.Length+1);
                nEmails[nEmails.Length - 1] = email;
                emails = nEmails;
            }
        }
        
        /**
         * Function to encrypt the string plaintext using the RSA encryption formula
         * e - power to raise the message to
         * n - value to mod the message by
         * return - base64 encoded string
         */
        public string encodeText(BigInteger e, BigInteger n, string plaintext)
        {
            var asciArr = Encoding.ASCII.GetBytes(plaintext);
            BigInteger msgval = new BigInteger(asciArr);
            var res = BigInteger.ModPow(msgval, e, n);
            var s = res.ToByteArray();
            return Convert.ToBase64String(res.ToByteArray());
        }
        
        /**
         * Function to decrypt the string ciphertext using the RSA decryption formula
         * d - power to raise the message to
         * n - value to mod the message by
         * return - message string
         */
        public string decodeText(BigInteger d, BigInteger n, string ciphertext)
        {
            
            var asciArr = Convert.FromBase64String(ciphertext);
            BigInteger msgVal = new BigInteger(asciArr);
            BigInteger res = BigInteger.ModPow(msgVal,d,n);
            return Encoding.ASCII.GetString(res.ToByteArray());
        }

        

        //Helper function to calculate the mod inverse of a bigint a mod n
        public BigInteger modInverse(BigInteger a, BigInteger n)
        {
            BigInteger i = n, v = 0, d = 1;
            while (a>0) {
                BigInteger t = i/a, x = a;
                a = i % x;
                i = x;
                x = d;
                d = v - t*x;
                v = x;
            }
            v %= n;
            if (v<0) v = (v+n)%n;
            return v;
        }

        
        /**
         * Send key function which takes an email, registers it as a valid receiver and send
         * it to the server with the public key attached
         */
        public async Task sendKey(string email)
        {
            try
            {
                string pubkey = System.IO.File.ReadAllText("public.key");
                var msg = new KeyMsg();
                msg.email = email;
                msg.key = pubkey;
                var json = Serialize(msg, typeof(KeyMsg));
                var content = new StringContent(json,Encoding.UTF8,"application/json");
                string seckey = System.IO.File.ReadAllText("private.key");
                var secret = Deserialize<PrivKey>(seckey);
                secret.addEmail(email);
                var updated = Serialize(secret, typeof(PrivKey));
                HttpResponseMessage requestMessage =
                    await client.PutAsync("http://kayrun.cs.rit.edu:5000/Key/" + email, content);
            
                System.IO.File.WriteAllText("private.key",updated);
                Console.WriteLine("Key saved");
            }
            catch (FileNotFoundException)
            {
                Console.WriteLine("No key files exist or one was damaged");
                throw;
            }
        }

        /**
         * getKey function which retrieves the encoded public key associated with email
         * from the server, it creates a emailname.key file to store this information
         */
        public async Task getKey(string email)
        {
            HttpResponseMessage responseMessage = await client.GetAsync("http://kayrun.cs.rit.edu:5000/Key/" + email);
            string responseBody = await responseMessage.Content.ReadAsStringAsync();
            if (responseBody.Equals(""))
            {
                Console.WriteLine("No key exists for {0}",email);
                return;
            }
            KeyMsg k = Deserialize<KeyMsg>(responseBody);
            System.IO.File.WriteAllText(email + ".key", k.key);
        }
        
        /**
         * sendMsg function takes an email string and attempts to send the plaintext input to that
         * email on the server by encrypting it with the associated public key
         */
        public async Task sendMsg(string email, string plaintext)
        {
            try
            {
                var pkey = System.IO.File.ReadAllText(email + ".key");
                var pkeyVals = fileParse(Convert.FromBase64String(pkey));
                var encodedmsg = encodeText(pkeyVals[1], pkeyVals[3], plaintext);
                var mesg = new MessMsg();
                mesg.email = email;
                mesg.content = encodedmsg;
                var json = Serialize(mesg, typeof(MessMsg));
                var content = new StringContent(json,Encoding.UTF8,"application/json");
                string q = "http://kayrun.cs.rit.edu:5000/Message/" + email;
                HttpResponseMessage requestMessage =
                    await client.PutAsync(q, content);
                Console.WriteLine("Message written");
            }
            catch (FileNotFoundException)
            {
                Console.WriteLine("Key does not exist for {0}",email);
                return;
            }
        }

        /**
         * getMsg retrieves a message for email if that email has been registered with the private key
         * then attempts to decrpyt the servers message using the private key
         */
        public async Task getMsg(string email)
        {
            try
            {
                var skey = System.IO.File.ReadAllText("private.key");
                var keyobj = Deserialize<PrivKey>(skey);
                bool contained = false;
                foreach (var s in keyobj.emails)
                {
                    if (s.Equals(email))
                    {
                        contained = true;
                    }
                }

                if (!contained)
                {
                    Console.WriteLine("Key does not exist for {0}", email);
                    return;
                }

                var pkey = fileParse(Convert.FromBase64String(keyobj.key));
                HttpResponseMessage responseMessage =
                    await client.GetAsync("http://kayrun.cs.rit.edu:5000/Message/" + email);
                var body = await responseMessage.Content.ReadAsStringAsync();
                MessMsg m = Deserialize<MessMsg>(body);
                string dmsg = decodeText(pkey[1], pkey[3], m.content);
                Console.WriteLine(dmsg);
            }
            catch (FileNotFoundException)
            {
                Console.WriteLine("Key file does not exist");
            }
        }

        /**
         * keyGen function generates a keypair (public and private keys) and store
         * them locally on the disk (in files called public.key and private.key respectively), as
         * encoded keys
         */
        public void keyGen(BigInteger keysize)
        {
            var LE = BitConverter.IsLittleEndian;
            
            BigInteger psize = (int)keysize / 2;
            Random random = new Random();
            var off = random.Next(-(int) keysize / 10, (int) keysize / 10);
            psize -= off;
            BigInteger qsize = keysize - psize;
            BigInteger p = 35461;
            BigInteger q = 21799;
            BigInteger N = p * q;
            BigInteger r = (p - 1) * (q - 1);
            BigInteger E = 11843;
            BigInteger D = modInverse(E, r);
            BigInteger x = 8827;
            BigInteger fuk = BigInteger.ModPow(x,E,N);
            var Earr = E.ToByteArray();
            try
            {
                Earr = E.ToByteArray();
            }
            finally
            {
                Console.WriteLine("dang");
            }

            //if(LE) Array.Reverse(Earr);
            var Elen = (BigInteger)E.GetByteCount();
            var lilE = Elen.ToByteArray();
            Array.Resize(ref lilE,4);
            if(LE) Array.Reverse(lilE);
            var Darr = D.ToByteArray();
            //if(LE) Array.Reverse(Darr);
            var Dlen = (BigInteger)D.GetByteCount();
            var lilD = Dlen.ToByteArray();
            Array.Resize(ref lilD,4);
            if(LE) Array.Reverse(lilD);
            var Narr = N.ToByteArray();
            //if(LE) Array.Reverse(Narr);
            var Nlen = (BigInteger)N.GetByteCount();
            var lilN = Nlen.ToByteArray();
            Array.Resize(ref lilN,4);
            if(LE) Array.Reverse(lilN);
            var ekeylist = new List<byte>();
            ekeylist.AddRange(lilE);
            ekeylist.AddRange(Earr);
            ekeylist.AddRange(lilN);
            ekeylist.AddRange(Narr);
            byte[] ekeyArr = ekeylist.ToArray(); 
            var dkeylist = new List<byte>();
            dkeylist.AddRange(lilD);
            dkeylist.AddRange(Darr);
            dkeylist.AddRange(lilN);
            dkeylist.AddRange(Narr);
            byte[] dkeyArr = dkeylist.ToArray(); 
            var secretkey = new PrivKey();
            secretkey.emails = new String[0];
            secretkey.key = Convert.ToBase64String(dkeyArr);
            System.IO.File.WriteAllText("private.key",Serialize(secretkey,typeof(PrivKey)));
            System.IO.File.WriteAllText("public.key",Convert.ToBase64String(ekeyArr));
            
        }

        //Helper function which splits the byte array from keyString found in
        //messages into a more easily usable array of big ints, lile BigE liln bigN
        private static BigInteger[] fileParse(byte[] arr)
        {
            var LE = BitConverter.IsLittleEndian;
            byte[] leArr = arr.SubArray(0, 4);
            if(LE) Array.Reverse(leArr);
            BigInteger littleE = new BigInteger(leArr);
            byte[] beArr = arr.SubArray(4, littleE);
            //if(LE) Array.Reverse(beArr);
            BigInteger bigE = new BigInteger(beArr);
            byte[] lnArr = arr.SubArray(4+littleE, 4);
            if(LE) Array.Reverse(lnArr);
            BigInteger littleN = new BigInteger(lnArr);
            byte[] bnArr = arr.SubArray(8+littleE, littleN);
            //if(LE) Array.Reverse(bnArr);
            BigInteger bigN = new BigInteger(bnArr);
            
            BigInteger[] res = new BigInteger[4];
            res[0] = littleE;
            res[1] = bigE;
            res[2] = littleN;
            res[3] = bigN;
            return res;

        }
        
        static readonly HttpClient client = new HttpClient();
        
        //Helper function to print the command line tips
        public void printHelp()
        {
            Console.WriteLine("dotnet run <option> <other arguments>");
            Console.WriteLine("\t- option - Messenger Command to execute");
            Console.WriteLine("\t- other arguments other arguments for commands");
            return;
        }
        
        /**
         * Main function which accepts and parses command line inputs and executes the valid messenger
         * commands
         */
        static async Task Main(string[] args)
        {
            SecureMessenger primary = new SecureMessenger();
            primary.keyGen((BigInteger)1233333333);
            if (args.Length < 2)
            {
                Console.WriteLine("Too few arguments");
                primary.printHelp();
                return;
            }
            switch (args[0])
            {
                case "keyGen":
                    if (args.Length != 2)
                    {
                        Console.WriteLine("1 Other Argument required, {0} found",args.Length-1);
                        return;
                    }
                    primary.keyGen(int.Parse(args[1]));
                    break;
                case "sendKey":
                    if (args.Length != 2)
                    {
                        Console.WriteLine("1 Other Argument required, {0} found",args.Length-1);
                        return;
                    }

                    await primary.sendKey(args[1]);
                    break;
                
                case "getKey":
                    if (args.Length != 2)
                    {
                        Console.WriteLine("1 Other Argument required, {0} found",args.Length-1);
                        return;
                    }

                    await primary.getKey(args[1]);
                    break;
                case "sendMsg":
                    if (args.Length != 3)
                    {
                        Console.WriteLine("1 Other Argument required, {0} found",args.Length-1);
                        return;
                    }

                    await primary.sendMsg(args[1], args[2]);
                    break;
                case "getMsg":
                    if (args.Length != 2)
                    {
                        Console.WriteLine("1 Other Argument required, {0} found",args.Length-1);
                        return;
                    }

                    await primary.getMsg(args[1]);
                    break;
                default:
                    Console.WriteLine("Invalid command entered");
                    return;
            }
            return;
        }
    }
}