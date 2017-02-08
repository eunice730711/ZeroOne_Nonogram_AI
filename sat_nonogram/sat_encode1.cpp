//
//  main.cpp
//  milestone1
//
//  Created by Emily on 2016/11/6.
//  Copyright © 2016年 Emily. All rights reserved.
//
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
#include <map>
#include <cmath>
#include <queue>
#include <stack>
#include <set>
#include <deque>
#include <fstream>
#include <time.h>

using namespace std;
#define COL 25
#define ROW 25
#define LENGTH 25
#define CONSTRAINT10 54
#define CONSTRAINT25 39
#define CONSTRAINT5 59
#define REP(i,x) for (int i=0; i<(x); i++)
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
struct pos
{
    int x,y;
};
struct variable
{
    int idx,val;
    int preval;
    int level,order,implyc;
};
// NONOGRAM
//int LENGTH;
int bb[COL]; // using in Allpossible : blocks between numbers
int posline; // using in Allpossible : assign particular line
Table row_mulpossible[ROW], col_mulpossible[COL]; // store all possibles
fstream infile,outfile,outpuzzle;
Description col[COL],row[ROW]; //store description
int variables[30][30];
vector<int> clause;
map<int,pos> m;
int fidx=LENGTH*LENGTH+1; //fack variables
int ans[LENGTH][LENGTH];

// SAT SOLVER
vector<vector<int> > clauses;
int maxVarIndex;
vector<vector<int> > pw,nw;
vector<pair<int,int> > watch; // watching literal in clauses
vector<variable> vars,assign; // var status ( for 2 literal watching )
vector<int> unit; //unit clauses
vector<double> act_score;
set<int> satv,assignv; // record ALL SAT clauses and ALL assigned var


// ---CHECK CLAUSE SIZE BIGGER THAN 50
bool checkbigger = false;
// ---RESTART---
double threshold=150, multiply = 1.5, conflict_times=0;

void mapping()
{
    int idx = 1;
    REP(i,ROW) REP(j,COL){
        variables[i][j]=idx;
        m[idx].x=i,m[idx].y=j;
        idx++;
    }
}
void getvariables(uint64_t number,int line, bool column)
{
    char bitset[64];
    fidx +=1;
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
    for(uint64_t i=CONSTRAINT25; i<64; ++i)
    {
        //cout << bitset[i] << endl;
        clause.clear();
        clause.push_back(-fidx);
        if(column)
        {
            if(bitset[i] == '1') clause.push_back(variables[i-CONSTRAINT25][line]); //相反
            else clause.push_back(-variables[i-CONSTRAINT25][line]);
            //clause.push_back(0);
            clauses.push_back(clause);
        }
        else
        {
            if(bitset[i] == '1') clause.push_back(variables[line][i-CONSTRAINT25]);
            else clause.push_back(-variables[line][i-CONSTRAINT25]);
            //clause.push_back(0);
            clauses.push_back(clause);
        }
    }
}
void Read(string title)
{
    getline(infile,title);
    for(int i=0; i<COL ; i++)
    {
        string line;
        int num=0,ind=1,t=LENGTH,sum=0;
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
        // for(int j=1; j<=col[i].dsize; j++)
        // {
        //     cout << col[i].des[j] << ' ';

        // }
        // cout << endl;
        //cout << col[i].dsize << ' ' << col[i].remain << ' ' << col[i].dsum << endl;
    }
    for(int i=0; i<ROW ; i++)
    {
        string line;
        int num=0,ind=1,t=LENGTH,sum=0;
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
        // for(int j=1; j<=row[i].dsize; j++)
        // {
        //     cout << row[i].des[j] << ' ';
        // }
        // cout << endl;
        //cout << col[i].dsize << ' ' << col[i].remain << ' ' << col[i].dsum << endl;
    }
}
///--------------------probability(not used)
void inital()
{
    for(int i=0; i<COL; i++)
    {
        row_mulpossible[i].psize=0;
        col_mulpossible[i].psize=0;
    }
}

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
        col_mulpossible[posline].allpos[col_mulpossible[posline].psize++] = poss;     
        getvariables(poss, posline, 1);
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
        row_mulpossible[posline].allpos[row_mulpossible[posline].psize++] = poss;
        getvariables(poss, posline, 0);
        
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
    int number=0;
    for(int i=0; i<COL ; i++)
    {
        posline = i;
        int tmpf = fidx+1;
        ColAllpossible(col[i].remain,col[i].dsize);
        clause.clear();
        for(int i=tmpf;i<=fidx;i++)
        {
            clause.push_back(i);
        }
        //clause.push_back(0);
        clauses.push_back(clause);
        //cout << col_mulpossible[posline].psize << endl;

    }
    for(int i=0; i<ROW ; i++)
    {
        posline = i;
        int tmpf = fidx+1;
        RowAllpossible(row[i].remain,row[i].dsize);
        clause.clear();
        for(int i=tmpf;i<=fidx;i++)
        {
            clause.push_back(i);
        }
        //clause.push_back(0);
        clauses.push_back(clause);
        //cout << row_mulpossible[posline].psize << endl;
    }
    //  TEST
    for(int i=0;i<COL ;i++)
    {
        int sc = col_mulpossible[i].psize;
        int sr = row_mulpossible[i].psize;
        number += sc;
        number += sr;
    }
    //cout << number << endl;
}
void decode()
{
    for(int i=1;i<=LENGTH*LENGTH;i++)
    {
        int x,y;
        if(vars[i].val ==1) ans[m[i].x][m[i].y]=1;
        else ans[m[i].x][m[i].y]=0;
    }
    for(int i=0;i<LENGTH;i++)
    {
        for(int j=0;j<LENGTH;j++)
        {
            outpuzzle << ans[i][j] << ' ';
        }
        outpuzzle << endl;

    }
}
// MY SATSOLVER
void initial_watch()
{
    // This function set all watch literals in the beginning
    for(int i=0;i<clauses.size();i++) // watch
    {
        if(clauses[i].size()>=2) watch.push_back(make_pair(clauses[i][0],clauses[i][1]));
        else if(clauses[i].size()==1){  // clause only have one literal
            watch.push_back(make_pair(clauses[i][0],0)); //can delete???
            unit.push_back(clauses[i][0]); //unit clauses
        }
    }
}
void new_watch(vector<int> clause)
{
    // This funciton set new clause watch literals
    if(clause.size()==0) return; 
    int box1=0,box2=0;
    pair<int,int> tmpp(0,0);
    for(int i=0;i<clause.size();i++)
    {
          if(vars[abs(clause[i])].val == -1) // found literal not assign
          {
                if(box1==0)
                {
                    tmpp.first = clause[i];
                    box1=1;
                }
                else if(box2==0)
                {
                    tmpp.second = clause[i];
                    box2=1;
                }
                else if(box1==2)
                {
                    tmpp.first = clause[i];
                    box1=1;
                }
                else if(box2==2)
                {
                    tmpp.second = clause[i];
                    box2=1;
                }
                continue;
            }
            else
            {
                if(box1==0)
                {
                    tmpp.first = clause[i];
                    box1=2;
                }
                else if(box2==0)
                {
                    tmpp.second = clause[i];
                    box2=2;
                }
                else if(box1==2 && vars[abs(clause[i])].level > vars[abs(tmpp.first)].level)
                {
                    tmpp.first = clause[i];
                    box1=2;
                }
                else if(box2==2 && vars[abs(clause[i])].level > vars[abs(tmpp.second)].level)
                {
                    tmpp.second = clause[i];
                    box2=2;
                }
            }
    }

    watch.push_back(tmpp);
    clauses.push_back(clause);
    int idx = clauses.size()-1;
    if(tmpp.first !=0)
    {
        if(tmpp.first < 0) nw[abs(tmpp.first)].push_back(idx);
        else if(tmpp.first >0) pw[tmpp.first].push_back(idx);
    }
    if(tmpp.second !=0)
    {
        if(tmpp.second <0) nw[abs(tmpp.second)].push_back(idx);
        else if(tmpp.second >0) pw[tmpp.second].push_back(idx);
    }
}
void initial_var()
{
    // initial var & pw & nw
    // fill in zero index (we don't need it!)
    variable zero;
    vars.push_back(zero);
    vector<int> zeropw,zeronw;
    pw.push_back(zeropw),nw.push_back(zeronw);
    
    for(int i=1;i<=maxVarIndex;i++) // vars
    {
        variable tmpv;
        vector<int> tmppw,tmpnw;
        
        tmpv.idx = i;
        tmpv.level = -1; //unassign level
        tmpv.val = -1; //unassign value
        tmpv.preval = -1; 
        tmpv.order = -1;
        for(int j=0;j<watch.size();j++)
        {
            if(watch[j].first == i || watch[j].second == i) tmppw.push_back(j);
            if(watch[j].first == -i || watch[j].second == -i) tmpnw.push_back(j);
        }
        pw.push_back(tmppw);
        nw.push_back(tmpnw);
        vars.push_back(tmpv);
    }
}
void set_UNIT(deque<int> &tmpassign)
{
    for(int i=0;i<unit.size();i++)
    {
        int v = unit[i];
        if(v>0) vars[v].val = 1, vars[v].level = 0; // var = 1@0
        else if(v<0) vars[-v].val = 0, vars[-v].level = 0; // var = 0@0
        assign.push_back(vars[abs(v)]); //global assigned variables
        tmpassign.push_front(abs(v)); // assigned in the first round (became unit in the very beginning)
    }
}

int BCPLiteralWatching(int lev, deque<int> &tmpassign) // if true:return -1 ; if false:return conflict clauses
{
    int ord = 2;
    map<int,bool> check;
    while(!tmpassign.empty()) // check whether new imply varibles can imply new variables
    {
        int tmpi = tmpassign.front();
        //cout << "out: tmpi: " << tmpi << endl;
        // cout << "tmpi.preval: " << tmpi << ' ' << vars[abs(tmpi)].preval << endl;
        // cout << "tmpi.val: " << tmpi << ' ' << vars[abs(tmpi)].val << endl;
        assignv.insert(tmpi);
        tmpassign.pop_front();
        
        if(vars[abs(tmpi)].val == -1 && vars[abs(tmpi)].preval != -1)
        {
            vars[abs(tmpi)].val = vars[tmpi].preval;
            vars[abs(tmpi)].level = lev;
            vars[abs(tmpi)].order = ord;
            vars[abs(tmpi)].preval = -1;
            ord+=1;
            //assignv.insert(tmpi);
        }
        if(check[abs(tmpi)]) continue;
        check[abs(tmpi)]=true;
        //cout << "a: tmpi.val: " << tmpi << ' ' << vars[tmpi].val << endl;
        
        if(vars[tmpi].val == 1) // if val == 1 : check nw clauses
        {
            vector<int> deletions;
            //for(int i=0;i<pw[tmpi].size();i++) satv.insert(pw[tmpi][i]); //clauses became SAT
            for(int i=0;i<nw[tmpi].size();i++) // check every clauses stored in nw
            {
                vector<int> c = clauses[nw[tmpi][i]]; // c is the clause which we are deal with now!
                bool next = false, issat = false, first = false;
                if(tmpi == abs(watch[nw[tmpi][i]].first)) first = true; // var appear at first watch literal
                for(int j=0;j<c.size();j++)
                {
                    //check if not-assigned, not-watched
                    int tmpidx = c[j];
                    //check if this clause allready SAT (still have to do something...)
                    if((tmpidx > 0 && vars[abs(tmpidx)].val == 1) || (tmpidx < 0 && vars[abs(tmpidx)].val == 0)) issat = true;
                    //check if not-assigned, not-watched
                    if(vars[abs(tmpidx)].val == -1 && tmpidx!=watch[nw[tmpi][i]].first && tmpidx!=watch[nw[tmpi][i]].second)
                    {
                        if(first) watch[nw[tmpi][i]].first = tmpidx;
                        else watch[nw[tmpi][i]].second = tmpidx;
                        
                        //reset pw & nw
                        if(tmpidx >0) pw[tmpidx].push_back(nw[tmpi][i]); //reset pw
                        else nw[-tmpidx].push_back(nw[tmpi][i]); // reset nw
                        
                        //record deletions' index
                        deletions.push_back(nw[tmpi][i]);
                        next = true;
                        break;
                    }
                }
                if(next) continue; //next watching literal is setted
                int vind =0; //another watch literal
                if(first) vind = watch[nw[tmpi][i]].second;
                else vind = watch[nw[tmpi][i]].first;
                
                if((vind > 0 && vars[abs(vind)].val == 1) || ((vind < 0 && vars[abs(vind)].val == 0)) || issat)
                {
                    // cout << "test2" << endl;
                    // another watch literal already assign to true
                    satv.insert(nw[tmpi][i]);
                }
                else if(vars[abs(vind)].val == -1)
                {
                    // cout << "test3" << endl;
                    // another watch literal has NOT been assigned
                    if(vind >0)
                    {
                        vars[abs(vind)].implyc = nw[tmpi][i];
                        vars[abs(vind)].preval = 1;
                        // cout << abs(vind) << ' ' << '1' << endl;
                    }
                    else
                    {
                        vars[abs(vind)].implyc = nw[tmpi][i];
                        vars[abs(vind)].preval = 0;
                        //cout << abs(vind) << ' ' << '0' << endl;
                    }
                    
                    vars[abs(vind)].implyc = nw[tmpi][i];
                    //assignv.insert(abs(vind));
                    tmpassign.push_back(abs(vind)); //new imply variable
                }
                else if( ((vind > 0 && vars[abs(vind)].val == 0) || (vind < 0 && vars[abs(vind)].val == 1)) && !issat) // conflict
                {
                	//cout << "2nw:"<< nw[tmpi][i] << endl;
                	int clauseno = nw[tmpi][i];
                    // another watch literal already assign to false
                    for(int j=0;j<deletions.size();j++)
                    {
                        nw[tmpi].erase(remove(nw[tmpi].begin(),nw[tmpi].end(),deletions[j]),nw[tmpi].end());
                    }
                    // RETURN CONFLICT CLAUSE
                    return clauseno;
                }
            }
            //ERASE BY VALUE
            for(int j=0;j<deletions.size();j++)
            {
                nw[tmpi].erase(remove(nw[tmpi].begin(),nw[tmpi].end(),deletions[j]),nw[tmpi].end());
            }
        }
        else if(vars[tmpi].val == 0)
        {
            //cout << "b: tmpi.val: " << tmpi << ' ' << vars[tmpi].val << endl;
            vector<int> deletions;
            //cout << "tmpi: " << tmpi << endl;
            //cout << nw[tmpi].size() << ' ' << cout << pw[tmpi].size() << endl;
            //for(int i=0;i<nw[tmpi].size();i++) satv.insert(nw[tmpi][i]);
            for(int i=0;i<pw[tmpi].size();i++) // check every clauses stored in pw
            {
                vector<int> c = clauses[pw[tmpi][i]];
                bool next = false, issat = false, first = false;
                if(tmpi == abs(watch[pw[tmpi][i]].first)) first = true; // var appear at first watch literal
                
                // CHECK THE THIS CLAUSE
                for(int j=0;j<c.size();j++)
                {
                    int tmpidx = c[j];
                    if((c[j] > 0 && vars[abs(tmpidx)].val == 1) || (c[j] < 0 && vars[abs(tmpidx)].val == 0)) issat = true;
                    if(vars[abs(tmpidx)].val == -1 && tmpidx!=watch[pw[tmpi][i]].first && tmpidx!=watch[pw[tmpi][i]].second)
                    {
                        if(first) watch[pw[tmpi][i]].first = tmpidx;
                        else watch[pw[tmpi][i]].second = tmpidx;
                        
                        // SET PW OR NW
                        if(tmpidx >0) pw[tmpidx].push_back(pw[tmpi][i]); //reset pw
                        else nw[-tmpidx].push_back(pw[tmpi][i]); // reset nw
                        // RECORD DELETIONS' INDEX
                        deletions.push_back(pw[tmpi][i]);
                        next = true;
                        break;
                    }
                    
                }
                if(next) continue;//next watching literal is setted
                //cout << "d: tmpi.val: " << tmpi << ' ' << vars[tmpi].val << endl;
                int vind =0; //another watch literal
                if(first) vind = watch[pw[tmpi][i]].second;
                else vind = watch[pw[tmpi][i]].first;
                if((vind > 0 && vars[abs(vind)].val == 1) || ((vind < 0 && vars[abs(vind)].val == 0)) || issat)
                {
                    satv.insert(pw[tmpi][i]);
                }
                else if(vars[abs(vind)].val == -1)
                {
                    if(vind >0)
                    {
                        vars[abs(vind)].implyc = pw[tmpi][i];
                        vars[abs(vind)].preval = 1;
                    }
                    else
                    {
                        vars[abs(vind)].implyc = pw[tmpi][i];
                        vars[abs(vind)].preval = 0;
                    }
                    
                    vars[abs(vind)].implyc = pw[tmpi][i];
                    tmpassign.push_back(abs(vind));
                }
                else if( ((vind > 0 && vars[abs(vind)].val == 0) || (vind < 0 && vars[abs(vind)].val == 1)) && !issat) // conflict
                {
                	int clauseno = pw[tmpi][i];
                    for(int j=0;j<deletions.size();j++)
                    {
                        pw[tmpi].erase(remove(pw[tmpi].begin(),pw[tmpi].end(),deletions[j]),pw[tmpi].end());
                    }
                    // GET CONFLICT CLAUSE
                    return clauseno;
                }
            }
            for(int j=0;j<deletions.size();j++)
            {
                pw[tmpi].erase(remove(pw[tmpi].begin(),pw[tmpi].end(),deletions[j]),pw[tmpi].end());
            }
        }
        
    }
    return -1;
}

void heuristic(priority_queue<pair<double,int> > &scores, vector<int> newc)
{
    //cout << "heuristic decide: " << decide.size() << endl;
    priority_queue<pair<double,int> > newscores;
    double constant=0.95;
    set<int> span;
    map<int,bool> add;
    vector<int>::iterator it;
    for(int i=0;i<newc.size();i++)
    {
        //vars[abs(newc[i])].act_score += 1;
        act_score[abs(newc[i])] +=1;
        add[abs(newc[i])]=true;
        span.insert(vars[abs(newc[i])].level);
    }
    for(int i=1;i<=maxVarIndex;i++)
    {
        if(add[i] == false) (act_score[i])*=constant;
        if(vars[i].val == -1) newscores.push(make_pair(act_score[i],i));
    }
    scores = newscores;
}
vector<int> firstUIP(int clause,int level) // get new clause into database
{
    vector<int> newc;
    map<int,bool> exist;
    vector<int> antec,nowc;
    //cout << "---firstUIP---" << endl;
    int p = 0, num =0, maxord =0, prep=0;
    for(int i=0;i<clauses[clause].size();i++) // count the number
    {
        int idx = abs(clauses[clause][i]);
        //cout << idx << ' ' << vars[idx].level << ' ' << vars[idx].order << endl;
        if(vars[idx].level !=0) nowc.push_back(clauses[clause][i]);
        if(vars[idx].level == level) // && vars[idx].order!=1
        {
            num+=1;
            if(vars[idx].order > maxord)
            {
                maxord = vars[idx].order;
                p = idx;
            }
        }
    }
    if(num <= 1) return nowc;
    antec = clauses[vars[p].implyc];
    
    do // clause has more than one literal assigned at current decision level
    {
        newc = vector<int>();
        exist = map<int,bool>();
        antec = clauses[vars[p].implyc];
        prep=0, num=0, maxord=0;
        
        // RESOLVE (C, antec(p), p)
        for(int i=0;i<nowc.size();i++)
        {
            if(abs(nowc[i])!= p && exist[nowc[i]] == false && vars[abs(nowc[i])].level !=0)
            { 
                newc.push_back(nowc[i]);
                exist[nowc[i]] = true;
                if(vars[abs(nowc[i])].level == level) // && vars[abs(newc[i])].order !=1
                {
                    //cout << 'd' << newc.size() << endl;
                    num +=1;
                    if(vars[abs(nowc[i])].order > maxord)
                    {
                        maxord = vars[abs(nowc[i])].order;
                        prep = abs(nowc[i]);
                    }
                }
            }       
        }
        for(int i=0;i<antec.size();i++)
        {
            if(abs(antec[i])!= p && exist[antec[i]] == false && vars[abs(antec[i])].level !=0) 
            {
                newc.push_back(antec[i]);
                exist[antec[i]] = true;
                if(vars[abs(antec[i])].level == level) // && vars[abs(newc[i])].order !=1
                {
                    num +=1;
                    if(vars[abs(antec[i])].order > maxord)
                    {
                        maxord = vars[abs(antec[i])].order;
                        prep = abs(antec[i]);
                    }
                }
            }
        }
        nowc = newc;
        p = prep;
    }while(num > 1);
    return newc;
}
int backlevel(vector<int> clause,int level)
{
    int maxlev = 0;
    checkbigger = false;
    conflict_times +=1;

    if(clause.size() == 1) // WHEN CLAUSE'S SIZE IF BIGGER THAN 50: DISCARD
    {
        return 0;
    }
    if(clause.size()>100) // take out the limitation of clause size 50
    {
        checkbigger = true;
        return 0;
    }
    if(conflict_times > threshold) // RESTART
    {
        checkbigger = true;
        threshold *= multiply;
        conflict_times =0;
        return 0;
    }
    for(int i=0;i<clause.size();i++)
    {
       // cout << clause[i] << ' ' << vars[abs(clause[i])].level << ' ' << vars[abs(clause[i])].order << endl;
        if(vars[abs(clause[i])].level != level) // || (vars[abs(clause[i])].level == level && vars[abs(clause[i])].order == 1)
        {
            maxlev = max(maxlev,vars[abs(clause[i])].level);
        }
    }
    if(maxlev == 0 && clause.size()!=1) return level;
    return maxlev;
}
bool DPLL() //ITERATIVE DPLL
{
    // ---DECLARE---
    int level = 0, back_level = 0, conflict_clause = 0; //begin assign from level one
    deque<int> tmpassign; // record assignment in this level
    priority_queue<pair<double,int> > decision; // store the scores of variables
    map<int,set<int> > save; // record all assignv in each level
    map<int,vector<variable> > levelvars; // store var in every levels
    vector<int> decide;
    bool conflict = false;
    int varidx = 0;
    bool check = false;

    // ---FIRST LEVEL ASSIGN (FROM PROBLEM GIVEN)---
    set_UNIT(tmpassign);
    if(BCPLiteralWatching(level,tmpassign)!=-1)
    {
        // if conflict with assignments at level 0 --> UNSAT
        return false;
    }
    save[level]=assignv; // save assign variable in level 0
    levelvars[level]=vars;

    // ---INITIAL Heuristic SCORES---
    act_score.push_back(0.0);
    for(int i=1;i<=maxVarIndex;i++)
    {
        act_score.push_back(0.0);
        if(vars[i].val == -1) decision.push(make_pair(0.0,i));
    }
    // ---BEGIN SOLVING---
    while(!decision.empty())
    {
        if(assignv.size() == maxVarIndex)
        {
            for(int i=0;i<clauses.size();i++)
                for(int j=0;j<clauses[i].size();j++)
                {
                    if((clauses[i][j]<0 && vars[abs(clauses[i][j])].val == 0) || (clauses[i][j]>0 && vars[abs(clauses[i][j])].val == 1))
                    {
                        satv.insert(i);
                    }
                }
        }
        if(satv.size() == clauses.size()) return true; //every var have been assign and all clauses became SAT
        
        // --- BEGIN ---
        if(!check)
        {
            tmpassign = deque<int>();
            satv = set<int>();
            
            if(!conflict)
            {
                varidx = decision.top().second;
                decision.pop();
                if(vars[varidx].val != -1)
                {
                    assignv.insert(varidx);
                    continue;
                }
                decide.push_back(varidx);
                level +=1;
            }
            else
            {
                varidx = decide.back();
            }

            //cout << "no continue" << endl;
            if(vars[varidx].val != -1) continue;
            if(!conflict) vars[varidx].val =0;
            else vars[varidx].val = 1;

            //cout << "varidx" << varidx << ": " << vars[varidx].val << endl;
            vars[varidx].level = level;
            vars[varidx].order = 1;
            tmpassign.push_front(varidx);
            assignv.insert(varidx);
            
        }
        // BCP
        conflict_clause = BCPLiteralWatching(level,tmpassign);
        if(conflict_clause == -1) // No conflict
        {
            // cout << "No conflict!" << endl;
            save[level]=assignv;
            levelvars[level]=vars;
            conflict = false;
            check = false;
            continue;
        }
        else // CONFLICT
        {
            // cout << "Conflict1" << endl;
            vector<int> newclause = firstUIP(conflict_clause,level);
            if(newclause.size()==0) return false;
            back_level = backlevel(newclause,level); // GET BACK LEVEL
            level = back_level;

            if(back_level == 0) // EVERYTHING START FORM BEGINNING
            {

                conflict = false; 
                vars = levelvars[0];
                if(!checkbigger)
                {
                    // Learned a new variable
                    if(newclause[0]>0) vars[newclause[0]].val =1;
                    else vars[abs(newclause[0])].val =0;
                    vars[abs(newclause[0])].level =0;
                    new_watch(newclause);
                }
                decide = vector<int>(); // CLEAR DECLARE
                heuristic(decision,newclause);
                assignv = save[0];
                assignv.insert(abs(newclause[0]));
                save[0]=assignv;
                levelvars[0]=vars;
                tmpassign.push_front(abs(newclause[0]));
                check = true; // go to BCP immediately
            } 
            else // BACK TO THE LEVEL
            {
                conflict =true; // guess 1 next time
                vars = levelvars[back_level-1];
                new_watch(newclause);
                decide.resize(back_level);
                heuristic(decision,newclause); // Get Heuristic Scores
                assignv = save[back_level];
                check = false;
            }
        }
    }

    //check last time
    if(assignv.size() == maxVarIndex)
        {
            for(int i=0;i<clauses.size();i++)
                for(int j=0;j<clauses[i].size();j++)
                {
                    if((clauses[i][j]<0 && vars[abs(clauses[i][j])].val == 0) || (clauses[i][j]>0 && vars[abs(clauses[i][j])].val == 1))
                    {
                        satv.insert(i);
                    }
                }
        }
    if(satv.size() == clauses.size()) return true; //every var have been assign and all clauses became SAT
    else return false;
    
}
int main(int argc, const char * argv[]) {
    
    ///---argv
    string input = argv[1];
    ///!!!!!!!!!!!!!!!!!!!!!!THIS MUST CHANGE
    string filename = input.substr(0,input.length()-4) + ".sat";
    fstream outfile;
    int start_time=clock();
    outfile.open(filename.c_str(),ios::out);
    ///---declare variables
    priority_queue<pair<double,int> > decision;
    
    //---read input files(.cnf)
    //parse_DIMACS_CNF(clauses, maxVarIndex, input.c_str());

    //---read nonogram puzzle
    infile.open(input.c_str(),ios::in);
    outpuzzle.open("puzzleans.txt",ios::out);
    string title;
    Read(title);
    mapping();
    ComputePossible();
    maxVarIndex = fidx;
    // cout << fidx << endl;
    // for(int i=0;i<clauses.size();i++)
    // {
    //     for(int j=0;j<clauses[i].size();j++)
    //     {
    //         cout << clauses[i][j] << ' ';
    //     }
    //     cout << endl;
    // }
    cout << "clause: "<< clauses.size() << endl;
    cout << "variables: " << maxVarIndex << endl;
    
    //heuristic
    initial_watch();
    initial_var();

    // //set_UNIT();
    if(!DPLL())
    {
        cout << "s UNSATISFIABLE" << endl;
        outfile << "s UNSATISFIABLE" << endl;
    }
    else
    {
        cout << "s SATISFIABLE" << endl;
        outfile << "s SATISFIABLE" << endl;
        outfile << "v ";
        for(int i=1;i<=maxVarIndex;i++)
        {
            if(vars[i].val == -1) vars[i].val=0;
            if(vars[i].val == 1) outfile << i << ' ';
            else outfile << -i << ' ';
        }
        outfile << '0' << endl;
    }
    int end_time = clock();
    //cout << end_time << endl;
    printf("Total run time = %f seconds\n",(end_time-start_time)/(double)CLOCKS_PER_SEC);
    decode();
    return 0;
}
