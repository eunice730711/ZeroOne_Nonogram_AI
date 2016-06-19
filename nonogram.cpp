#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <algorithm>
#include <bitset>
#include <string>
#include <fstream>
#include <string.h>
#include <queue>
#include <vector>
#include <time.h>
#include <map>

#define ROW 25
#define COL 25
#define ALL 50
#define LENGTH 25
#define NUM_PROBLEM 1000
using namespace std;
typedef pair<int,int> pointii;

//Hash table
const uint64_t nums[65] =
{
    0,1,3,7,15,31,63,127,255,511,1023,2047,4095,8191,16383,32767,65535,131071,262143,524287,1048575,2097151,4194303,8388607,16777215,33554431,
    67108863,134217727,268435455,536870911,1073741823,2147483647,4294967295,8589934591,17179869183,34359738367,68719476735,137438953471,274877906943,
    549755813887,1099511627775,2199023255551,4398046511103,8796093022207,17592186044415,35184372088831,70368744177663,140737488355327,281474976710655,
    562949953421311,1125899906842623,2251799813685247,4503599627370495,9007199254740991,18014398509481983,36028797018963967,72057594037927935,
    144115188075855871,288230376151711743,576460752303423487,1152921504606846975,
    2305843009213693951
};
const uint64_t ones[27] =
{
    1,9,41,169,681,2729,10921,43689,174761,699049,2796201,11184809,44739241,178956969,715827881,
    2863311529,11453246121,45812984489,183251937961,733007751849,2932031007401,11728124029609,
    46912496118441,187649984473769,750599937895081,3002399751580329,12009599006321321
};
//Variable
struct Description
{
    int des[LENGTH];
    int dsize=0;
    int remain=0;
    int dsum=0;
};
struct Table
{
    int allpos[55000];
    int possible[55000];
    int psize=0;
};

Description col[COL],row[ROW]; //store description
bool fixboard[ROW+2][COL+2],ifcompute[ROW+2][COL+2];
fstream infile,outfile,ansfile;
uint64_t rowss[ROW],colss[COL]; //string to store 01001000....
int bb[COL]; // using in Allpossible : blocks between numbers
int posline; // using in Allpossible : assign particular line
Table mulpossible[ALL]; // store all possibles
int line;

// tobinary
void decimal_to_binary(uint64_t number)
{
    char bitset[64];
    for(uint64_t i=0; i<64; ++i)
    {
        if((number & (static_cast<uint64_t>(1) << i)) != 0)
        {
            bitset[63-i] = '1';
        }
        else
        {
            bitset[63-i] = '0';
        }
    }
    for(uint64_t i=0; i<64; ++i)
    {
        cout << bitset[i];
    }
    cout << endl;
}
void bit_flip(int& m, int nth)
{
    m ^= 1 << nth;
}

///------------Read
void Read(string title)
{
    getline(infile,title);
    outfile << title << endl;
    for(int i=0; i<COL ; i++)
    {
        string line;
        int num=0,ind=1,t=25,sum=0;

        getline(infile,line);
        for(int j=0; j<line.size(); j++)
        {
            if(line[j]=='\t')
            {
                col[i].des[ind++]=num;
                t -= num+1;
                sum += num+1;
                num=0;
                continue;
            }
            num = num *10 + line[j]-'0';
        }
        col[i].des[ind++]=num;
        t -= num;
        sum += num +1;
        col[i].dsize = ind-1;
        col[i].remain=t;
        col[i].dsum=sum;

        //-----------Test------------
        for(int j=1; j<=col[i].dsize; j++)
        {
            outfile << col[i].des[j] << ' ';
        }
        outfile << endl;
    }
    for(int i=0; i<ROW ; i++)
    {
        string line;
        int num=0,ind=1,t=25,sum=0;
        getline(infile,line);
        for(int j=0; j<line.size(); j++)
        {
            if(line[j]=='\t')
            {
                row[i].des[ind++]=num;
                t -= num+1;
                sum += num+1;
                num=0;
                continue;
            }
            num = num *10 + line[j]-'0';
        }
        row[i].des[ind++]=num;
        t -= num;
        sum += num+1;
        row[i].dsize = ind-1;
        row[i].remain=t;
        row[i].dsum=sum;

        //-----------Test-------------
        for(int j=1; j<=row[i].dsize; j++)
        {
            outfile << row[i].des[j] << ' ';
        }
        outfile << endl;
    }
}

///-------------------initial
void inital()
{
    for(int i=0; i<COL; i++)
    {
        colss[i]=4503599627370493;
        rowss[i]=4503599627370493;
        mulpossible[i].psize=0;
        mulpossible[i+25].psize=0;
    }
}

///--------------------probability(not used)
void ColAllpossible(int totalz,int totalblock)
{
    if(totalblock == 0)
    {
        int block=0;
        unsigned int poss=0;
        for(int i=col[posline].dsize ; i>=1; i--)
        {
            poss += nums[col[posline].des[i]] << (block+bb[i-1]);
            block += col[posline].des[i] + bb[i-1] + 1;
        }
        mulpossible[posline].allpos[mulpossible[posline].psize++] = poss;
    }
    else
    {
        for(int i=0; i<=totalz; i++)
        {
            bb[totalblock-1]=i;
            ColAllpossible(totalz-i,totalblock-1);
        }
    }
}
void RowAllpossible(int totalz,int totalblock)
{
    if(totalblock == 0)
    {
        int block=0;
        unsigned int poss=0;
        for(int i=row[posline].dsize; i>=1 ; i--)
        {
            poss += nums[row[posline].des[i]] << (block+bb[i-1]);
            block += row[posline].des[i] + bb[i-1] + 1;
        }
        mulpossible[posline+25].allpos[mulpossible[posline+25].psize++] = poss;
    }
    else
    {
        for(int i=0; i<=totalz; i++)
        {
            bb[totalblock-1]=i;
            RowAllpossible(totalz-i,totalblock-1);
        }
    }
}
void ComputePossible()
{
    for(int i=0; i<COL ; i++)
    {
        posline = i;
        ColAllpossible(col[i].remain,col[i].dsize);
    }
    for(int i=0; i<ROW ; i++)
    {
        posline = i;
        RowAllpossible(row[i].remain,row[i].dsize);
    }
}
///----------------------Probability(not used)
double prob[55][25],finalp[25][25];
char guessb[30][30];
void pro()
{
    int binary;
    memset(prob,0,sizeof(prob));
    memset(finalp,0,sizeof(finalp));
    for(int j=0; j<50; j++)
    {
        for(int i=0; i<mulpossible[j].psize; i++)
        {

            for(int k = 24; k >=0 ; k--)
            {
                binary = (mulpossible[j].allpos[i] >> k) & 1; //0x01
                if(binary) prob[j][24-k]++;
            }
        }
        for(int i=0; i<25; i++)
        {
            prob[j][i]=prob[j][i]/(double)mulpossible[j].psize; //No. i grid of Line j or Row j
        }
    }
    for(int i=0; i<25; i++)
    {
        for(int j=0; j<25; j++)
        {
            if(prob[i][j]==1 || prob[j+25][i]==1) finalp[j][i]=1,guessb[j][i]='1';
            else finalp[j][i]=(prob[i][j]+prob[j+25][i])/(double)2.0;

        }
    }
}

//Line Solving

//1. fixable
bool fixboard0[ROW+2][COL+2],fixboard1[ROW+2][COL+2];
bool ifcompute0[ROW+2][COL+2],ifcompute1[ROW+2][COL+2];
bool fixarr1[ROW+2],fixarr0[ROW+2];
int low[ROW+2];

bool Fix(int i,int j,int line,bool ifrow);
bool Fix0(int i,int j,int line,bool ifrow)
{
    //cout << "fix0: " ;
    //cout << i << ' ' << j <<' ';
    if(ifcompute0[i][j]) return fixboard0[i][j];
    else
    {

        ifcompute0[i][j]=true;
        if(ifrow)
        {
            if(((rowss[line] >> ((i-1) << 1)) & 3 ) == 3 ||((rowss[line] >> ((i-1) << 1)) & 3 ) == 1 )
                return fixboard0[i][j]=Fix(i-1,j,line,ifrow);
            else return fixboard0[i][j]=false;
        }
        else
        {
            if(((colss[line] >> ((i-1) << 1)) & 3 ) == 3 ||((colss[line] >> ((i-1) << 1)) & 3 ) == 1 )
            {
                return fixboard0[i][j]=Fix(i-1,j,line,ifrow);
            }
            else return fixboard0[i][j]=false;
        }
    }
}
bool Fix1(int i,int j,int line,bool ifrow)
{
    //cout << "fix1: " ;
    // cout << i << ' ' << j << endl;
    if(ifcompute1[i][j]) return fixboard1;
    else
    {
        ifcompute1[i][j]=true;
        int dj;
        if(ifrow) // if the line is row
        {
            dj = row[line].des[j] ;
        }
        else dj = col[line].des[j];

        if(j>=1 && i>=dj+1)
        {
            uint64_t mask = nums[(dj+1) << 1] << ((i-dj-1) << 1);
            uint64_t tmps;
            if(ifrow) tmps=rowss[line] & mask;
            else tmps=colss[line] & mask;

            uint64_t cmp = ones[dj] << ((i-dj-1) << 1);
            if((cmp & tmps) == cmp) return fixboard1[i][j]=Fix(i-dj-1,j-1,line,ifrow);
            else return fixboard1[i][j]=false;
        }
        else return fixboard1[i][j]=false;
    }
}
bool Fix(int i,int j,int line,bool ifrow)
{
    // cout << i << ' ' << j << endl;
    if(ifcompute[i][j])
    {
        return fixboard[i][j];
    }
    else
    {
        ifcompute[i][j]=true;
        if(i==0 && j==0) return fixboard[i][j]=true;
        if(i==0 && j>=1) return fixboard[i][j]=false;
        else
        {

            bool fix00=Fix0(i,j,line,ifrow),fix11=Fix1(i,j,line,ifrow);
            return fixboard[i][j]=(fix00 || fix11);
        }
    }
}

//Paint
uint64_t paintboard0[ROW+2][COL+2],paintboard1[ROW+2][COL+2],paintboard[ROW+2][COL+2];
bool ifpaint0[ROW+2][COL+2],ifpaint1[ROW+2][COL+2],ifpaint[ROW+2][COL+2];

uint64_t Paint(int i,int j,int line,bool ifrow); //declare before Paint1 & Paint0
uint64_t Paint1(int i,int j,int line,bool ifrow)
{
    //  cout << "paint1: ";
    //  cout << i << ' ' << j << endl;
    if(ifpaint1[i][j]) return paintboard1[i][j];
    else
    {

        ifpaint1[i][j]=true;

        int dj=0;
        if(ifrow) dj=row[line].des[j];
        else dj=col[line].des[j];
        return paintboard1[i][j]=(Paint(i-dj-1,j-1,line,ifrow)+(ones[dj]<<((i-dj-1)*2)));
    }
}
uint64_t Paint0(int i,int j,int line,bool ifrow)
{
    //cout << "paint0: " ;
    // cout << i << ' ' << j<< endl;
    if(ifpaint0[i][j]) return paintboard0[i][j];
    else
    {
        uint64_t tmp=1;
        return paintboard0[i][j]=((Paint(i-1,j,line,ifrow))+(tmp<<((i-1)*2)));
    }
}
uint64_t Paint(int i,int j,int line,bool ifrow)
{
    // cout << i << ' ' << j << ": " ;
    if(ifpaint[i][j]) return paintboard[i][j];
    else
    {
        ifpaint[i][j]=true;
        if(i==0) return paintboard[i][j]=0;
        if(ifcompute[i][j]==false) Fix(i,j,line,ifrow);

        if(fixboard0[i][j] && !fixboard1[i][j]) //Paint0
        {
            uint64_t tmp0=Paint0(i,j,line,ifrow);
            return paintboard[i][j]=tmp0;
        }
        else if(fixboard1[i][j] && !fixboard0[i][j])//Paint1
        {
            uint64_t tmp1=Paint1(i,j,line,ifrow);
            return paintboard[i][j]=tmp1;
        }
        else if(fixboard1[i][j] && fixboard0[i][j])// Merge(Paint1,Paint0)
        {
            uint64_t p1=0,p2=0;
            p1=Paint1(i,j,line,ifrow);
            p2=Paint0(i,j,line,ifrow);
            return paintboard[i][j]=(p1|p2);
        }
    }
}
uint64_t tmprss[ROW+1],tmpcss[COL+1];
void ComputeAllFix() ///now unused
{
    for(int i=0; i<COL; i++) //particular COL
    {
        tmpcss[i]=0;
        memset(fixboard0,false,sizeof(fixboard0));
        memset(fixboard1,false,sizeof(fixboard1));
        memset(fixboard,false,sizeof(fixboard));
        memset(ifcompute0,false,sizeof(ifcompute0));
        memset(ifcompute1,false,sizeof(ifcompute1));
        memset(ifcompute,false,sizeof(ifcompute));
        memset(ifpaint0,false,sizeof(ifpaint0));
        memset(ifpaint1,false,sizeof(ifpaint1));
        memset(ifpaint,false,sizeof(ifpaint));

        if(Fix(COL+1,col[i].dsize,i,0)) //start compute fix and paint
        {
            colss[i]=Paint(COL+1,col[i].dsize,i,0);
        }
        //system("pause");
    }
    for(int i=0; i<ROW; i++) //particular ROW
    {
        tmprss[i]=0;
        memset(fixboard0,false,sizeof(fixboard0));
        memset(fixboard1,false,sizeof(fixboard1));
        memset(fixboard,false,sizeof(fixboard));
        memset(ifcompute0,false,sizeof(ifcompute0));
        memset(ifcompute1,false,sizeof(ifcompute1));
        memset(ifcompute,false,sizeof(ifcompute));
        memset(ifpaint0,false,sizeof(ifpaint0));
        memset(ifpaint1,false,sizeof(ifpaint1));
        memset(ifpaint,false,sizeof(ifpaint));
        if(Fix(ROW+1,row[i].dsize,i,1)) //start compute fix and paint
        {
            rowss[i]=Paint(ROW+1,row[i].dsize,i,1);
        }
    }
}

///--------Combine
priority_queue<pair<double,pointii> > pqb;
priority_queue<pair<double,pointii>,vector<pair<double,pointii> >,greater<pair<double,pointii> > > pqw;
vector<pointii> unpaint;
char testb[COL][ROW];
bool known[COL][ROW];
void Combine()
{
    unpaint.clear();
    for(int j=0; j<COL; j++)
    {
        for(int k=2; k<=50; k+=2)
        {
            if(((colss[j]>>k ) & 3 ) == 1)
            {
                testb[(k >> 1)-1][j]='0';
                known[(k >> 1)-1][j]=true;
            }
            else if(((colss[j]>> k) & 3 ) == 2 )
            {
                testb[(k >> 1)-1][j]='1';
                known[(k >> 1)-1][j]=true;
            }
            else
            {
                unpaint.push_back(pointii((k >> 1)-1,j));
            }
        }
    }
}

///Guess
uint64_t grow[ROW+1],gcol[COL+1];
vector<pointii> pixels;//newly painted pixels
bool Propagate()
{
    vector<pair<uint64_t,int> > lines;
    map<int,bool> inside;

    for(int i=0; i<ROW; i++) lines.push_back(make_pair(rowss[i],i+25)),inside[i+25]=true;
    for(int i=0; i<ROW; i++)  lines.push_back(make_pair(colss[i],i)),inside[i]=true;
    // cout << "propagate" << endl;

    while(!lines.empty())
    {

        memset(fixboard0,false,sizeof(fixboard0)); ///initialize
        memset(fixboard1,false,sizeof(fixboard1));
        memset(fixboard,false,sizeof(fixboard));
        memset(ifcompute0,false,sizeof(ifcompute0));
        memset(ifcompute1,false,sizeof(ifcompute1));
        memset(ifcompute,false,sizeof(ifcompute));
        memset(ifpaint0,false,sizeof(ifpaint0));
        memset(ifpaint1,false,sizeof(ifpaint1));
        memset(ifpaint,false,sizeof(ifpaint));

        pair<uint64_t,int> theline=lines.back();
        lines.pop_back();
        int index=theline.second;
        inside[index]=false;
        // cout << "index: " << index << endl;

        if(index<25) //cols
        {
            if(Fix(COL+1,col[index].dsize,index,0)) //if it can fix the description
            {
                gcol[index]=Paint(COL+1,col[index].dsize,index,0);//paint
                for(int i=2; i<=50; i+=2)
                {
                    if((((colss[index]>>i)&3)==3) && (((gcol[index]>>i)&3)==1)) // newly painted 01
                    {

                        if(((rowss[(i >> 1)-1]>>((index+1)*2))&3)==3)
                        {
                            uint64_t tmp1=1;
                            rowss[(i >> 1)-1] ^= tmp1 << (((index+1) << 1 )+1);
                            if(!inside[((i >> 1)-1)+25]) lines.push_back(make_pair(rowss[(i >> 1)-1],((i >> 1)-1)+25));
                        }
                        else if(((rowss[(i >> 1)-1]>>((index+1) << 1 ))&3)==2) //contradiction
                        {
                            cout << "no" <<endl;
                            system("pause");
                            return false;
                        }
                    }
                    else if((((colss[index]>>i)&3)==3) && (((gcol[index]>>i)&3)==2)) // newly painted 10
                    {

                        if(((rowss[(i >> 1)-1]>>((index+1) << 1))&3)==3)
                        {
                            uint64_t tmp1=1;
                            rowss[(i >> 1)-1] ^= tmp1 << (((index+1) << 1));
                            if(!inside[((i >> 1)-1)+25]) lines.push_back(make_pair(rowss[(i >> 1)-1],((i >> 1)-1)+25));
                        }
                        else if(((rowss[(i >> 1)-1]>>((index+1) << 1))&3)==1) //contradiction
                        {
                            cout << "no" <<endl;
                            system("pause");
                            return false;
                        }

                    }
                }
                colss[index]=gcol[index];
            }
            else return false;
        }
        else //rows
        {
            if(Fix(COL+1,row[index-25].dsize,index-25,1))
            {
                grow[index-25]=Paint(COL+1,row[index-25].dsize,index-25,1);

                for(int i=2; i<=50; i+=2)
                {
                    if((((rowss[index-25]>>i)&3)==3) && (((grow[index-25]>>i)&3)==1)) // newly painted 01
                    {
                        if(((colss[(i >> 1)-1]>>((index+1-25)*2))&3)==3)
                        {
                            uint64_t tmp1=1;
                            colss[(i >> 1)-1] ^= tmp1 << (((index+1-25) << 1)+1);
                            if(!inside[((i >> 1)-1)]) lines.push_back(make_pair(colss[(i >> 1)-1],((i >> 1)-1)));
                        }
                        else if(((colss[(i >> 1)-1]>>((index+1-25) << 1))&3)==2) //contradiction
                        {
                            cout << "no" <<endl;
                            system("pause");
                            return false;
                        }

                    }
                    else if((((rowss[index-25]>>i)&3)==3) && (((grow[index-25]>>i)&3)==2)) // newly painted 10
                    {
                        if(((colss[(i >> 1)-1]>>((index+1-25) << 1))&3)==3)
                        {
                            uint64_t tmp1=1;
                            colss[(i >> 1)-1] ^= tmp1 << (((index+1-25) << 1));
                            if(!inside[((i >> 1)-1)]) lines.push_back(make_pair(colss[(i >> 1)-1],((i >> 1)-1)));
                        }
                        else if(((colss[(i >> 1)-1]>>((index+1-25) << 1))&3)==1) //contradiction
                        {
                            cout << "no" <<endl;
                            system("pause");
                            return false;
                        }
                    }
                }
                rowss[index-25]=grow[index-25];
            }
            else return false;
        }
    }
    return true;
}

uint64_t oldrow[COL],oldcol[ROW],row0[COL],row1[COL],col0[ROW],col1[ROW];

bool FP1()
{
    int presize=-1;
    // cout << "fp" << endl;

    while(1)
    {
        for(int i=0; i<ROW; i++) oldcol[i]=colss[i],oldrow[i]=rowss[i]; //save old pattern
        if(!Propagate())
        {
            for(int i=0; i<ROW; i++) colss[i]=oldcol[i],rowss[i]=oldrow[i];
            cout << "falseeeeeeeeeeeeee" << endl;
            system("pause");
            return false;
        }
        Combine();

        if(unpaint.empty()) return true;
        if(presize!=unpaint.size()) presize=unpaint.size();
        else break;

        while(!unpaint.empty())
        {

            pointii newp=unpaint.back();
            unpaint.pop_back();

            int therow=newp.first,thecol=newp.second;
            bool black=false,white=false;
            uint64_t tmp1=1;

            for(int i=0; i<ROW; i++) oldcol[i]=colss[i],oldrow[i]=rowss[i]; //save old pattern
            rowss[therow] ^= tmp1 << (((thecol+1) << 1)+1); //change to zero
            colss[thecol] ^= tmp1 << (((therow+1) << 1)+1);
            white=Propagate();
            for(int i=0; i<ROW; i++) col0[i]=colss[i],row0[i]=rowss[i];
            for(int i=0; i<ROW; i++) colss[i]=oldcol[i],rowss[i]=oldrow[i];
            rowss[therow] ^= tmp1 << ((thecol+1) << 1); //change to one
            colss[thecol] ^= tmp1 << ((therow+1) << 1);
            black=Propagate();
            for(int i=0; i<ROW; i++) col1[i]=colss[i],row1[i]=rowss[i];
            for(int i=0; i<ROW; i++) colss[i]=oldcol[i],rowss[i]=oldrow[i];

            if(black && white)
            {
                for(int i=0; i<ROW; i++)
                {
                    colss[i] &= (col0[i] | col1[i]);
                    rowss[i] &= (row0[i] | row1[i]);
                }
            }
            else if(!black && white)
            {
                for(int i=0; i<ROW; i++)
                {
                    colss[i]=col0[i];
                    rowss[i]=row0[i];
                }
            }
            else if(!white && black)
            {
                for(int i=0; i<ROW; i++)
                {
                    colss[i]=col1[i];
                    rowss[i]=row1[i];
                }
            }
            else
            {
                //cout << "Conflict" << endl;
                return false;
            }
        }
    }
    return true;
}
int end_time,start_time;
bool Backtracking()
{

    end_time=clock();
    if(((end_time-start_time)/(double)CLOCKS_PER_SEC) > 25.0) return true;

    //if(unpaint.size()==0) return true;
    if(!FP1())
    {
        return false;
    }
    if(unpaint.size()==0) return true;

    uint64_t theoldcol[ROW],theoldrow[COL];
    for(int i=0; i<ROW; i++) theoldcol[i]=colss[i],theoldrow[i]=rowss[i]; //save old pattern

    if(!unpaint.empty())
    {
        pointii newp=unpaint.back();
        unpaint.pop_back();

        int therow=newp.first,thecol=newp.second;
        // cout <<"guess point->"<< therow << ' ' << thecol << endl;

        uint64_t tmp1=1;
        rowss[therow] ^= tmp1 << (((thecol+1) << 1)+1); //change to zero
        colss[thecol] ^= tmp1 << (((therow+1) << 1)+1);
        //Combine();

        Backtracking();
        if(unpaint.size()==0) return true;

        for(int i=0; i<ROW; i++) colss[i]=theoldcol[i],rowss[i]=theoldrow[i];

        rowss[therow] ^= tmp1 << ((thecol+1) << 1); //change to one
        colss[thecol] ^= tmp1 << ((therow+1) << 1);
        //Combine();

        Backtracking();
        if(unpaint.size()==0) return true;
    }
}
///check answers

void ReadAnswer(istream &filein,char ans[ROW][COL])
{
    string title;
    filein >> title; // read the question number
    int num;
    for(int i=0; i<ROW; i+=1)
    {
        for(int j=0; j<COL; j+=1)
        {
            filein >> num;
            if(num==1) ans[i][j]='1';
            else ans[i][j]='0';
        }
    }
}

vector<int> rowlimit[COL],collimit[ROW];
bool checklimit()
{
    for(int i=0; i<ROW; i++)
    {
        if(col[i].dsize==collimit[i].size())
        {
            for(int j=1; j<=col[i].dsize; j++)
            {
                if(col[i].des[j]!=collimit[i][j-1])
                {
                    cout << i << ' ' << j << endl;
                    cout << col[i].des[j] << ' ' << collimit[i][j] << endl;
                    return false;
                }
            }
        }
        else
        {
            cout << i << endl;
            return false;
        }
    }
    for(int i=0; i<ROW; i++)
    {
        if(row[i].dsize==rowlimit[i].size())
        {
            for(int j=1; j<=row[i].dsize; j++)
            {
                if(row[i].des[j]!=rowlimit[i][j-1])
                {
                    cout << i << ' ' << j << endl;
                    return false;
                }
            }
        }
        else
        {
            cout << i << endl;
            return false;
        }
    }
}
int main()
{
    infile.open("taai2014-question_from1.txt",ios::in);
    outfile.open("taai2014-question_from1_out.txt",ios::out);
    ansfile.open("taai2015-solution.txt",ios::in);
    int fp=0,pc=0;

    for(int i=1; i<=600; i++)
    {
        string title;
        Read(title);
        inital();
        cout <<"pp: "<< i << endl;

//        for(int j=0; j<COL; j++)
//        {
//            for(int k=0; k<ROW; k++)
//            {
//                testb[j][k]='u';
//                //testc[j][k]='u';
//                guessb[j][k]='u';
//                known[j][k]=false;
//            }
//        }
//        FP1();
//        Combine();
        start_time=clock();
        Backtracking();

//        for(int j=0; j<COL; j++)
//        {
//            for(int k=0; k<ROW; k++)
//            {
//                cout << testb[j][k] << ' ';
//            }
//            cout <<endl;
//        }
//        cout << endl;
        for(int j=0; j<ROW; j++) rowlimit[j].clear(),collimit[j].clear();
        for(int j=0; j<ROW; j++)
        {
            int c=0;
            for(int k=0; k<COL; k++)
            {
                if(testb[k][j]=='1') c++;
                else
                {
                    if(c>0)collimit[j].push_back(c);
                    c=0;
                }
            }
            if(c>0)collimit[j].push_back(c);
        }
        for(int j=0; j<ROW; j++)
        {
            int c=0;
            for(int k=0; k<COL; k++)
            {
                if(testb[j][k]=='1') c++;
                else
                {
                    if(c>0) rowlimit[j].push_back(c);
                    c=0;
                }
            }
            if(c>0) rowlimit[j].push_back(c);
        }
        if(checklimit()) cout << "good" << endl,pc++;
        else cout << "no" << endl;
        cout <<"pc: " << pc << endl;
        //  system("pause");
    }
    end_time = clock();
    cout << end_time << endl;
    cout << pc << endl;
    cout << fp << endl;
    return 0;
}
