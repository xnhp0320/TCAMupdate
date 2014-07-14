#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <list>
#include <map>
#include <iostream>
#include <algorithm>
#include <sstream>
#include <cmath>
#include <vector>
#include <arpa/inet.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <queue>

#include "update.h"
#include "tcam.h"

using namespace std;

#include "rulesutils.h"
#include "rtrie.h"

FILE *fpr;

void parseargs(int argc, char *argv[]) {
    int	c;
    while ((c = getopt(argc, argv, "r:")) != -1) {
        switch (c) {
            case 'r':
                fpr = fopen(optarg, "r");
                break;
            default:
                break;
        }
    }

    
    if(fpr == NULL){
        printf("can't open ruleset file\n");
        exit(-1);
    }

}


void build_graph(vector<pc_rule*> &pc, vector<struct node *> &G)
{
    G.resize(pc.size());
    for(size_t i = 0; i < pc.size(); i++) {
        pc[i]->n = new node();
        
        G[i] = pc[i]->n;
        G[i]->index = i;
        G[i]->r = pc[i];
    }

    //G[pc.size()-1].index = pc.size() - 1;

    ssize_t i = (ssize_t)(pc.size()-2);
    ssize_t j;

    for(;i>=0;i--){
        //G[i]->index = i;
        for(j=i+1;j<(ssize_t)pc.size();j++) {
            if(overlap(pc[i], pc[j])) {
                G[i]->out.push_back(G[j]);
                G[j]->in.push_back(G[i]);
            } 
        }
    }
}



void build_graph_fast(vector<pc_rule*> &pc, vector<struct node*> &G)
{
    G.resize(pc.size());
    for(size_t i = 0; i < pc.size(); i++) {
        pc[i]->n = new node();
        
        G[i] = pc[i]->n;
        G[i]->index = i;
        G[i]->r = pc[i];
    }

    struct overlap_trees ots;

    rule_boundary rb;
    init_boundary(rb);

    init_overlap_trees(&ots, rb, pc); 

    int i = pc.size() -2;
    for(; i>=0; i--) {
        vector<int> set;
        //vector<int> set2;
        find_overlap_rules(&ots, pc, pc[i], i+1, pc.size(), set);
        sort(set.begin(), set.end());
        //find_overlap_rules_slow(pc, pc[i], i+1, pc.size(), set);

        //if(set1 != set2) {
        //    cout<<"error"<< i <<endl;
        //}
        for(auto j = set.begin(); j != set.end(); j++) {
            G[i]->out.push_back(G[*j]);
            G[*j]->in.push_back(G[i]);
        }

    }


}

int dfs(struct node *n)
{
    if(n->move == -1) {
        if(n->out.size() != 0)
            n->move = dfs(n->out[0]) + 1;
        else 
            n->move = 1;
    }
    return n->move;
}



void compute_cost(struct node *n) 
{
    int contribute = 0;
    int remove = 0;
    //int node_cnt = 0;
    for(size_t i = 0; i < n->in.size(); i++) {
        auto parent = n->in[i];
        struct node * candidate;
        int gain = 0;

        if(parent->out.size() > 1) {
            candidate = (parent->out[1]);
            gain = candidate->move +1;
        }
        else {
            gain = 1;
        }
        
        if(parent->out[0] == n) {
            contribute += (n->move + 1);
            remove +=  gain;
            //node_cnt ++;
        }
    }
    
    n->cost = contribute - remove;
    //if(node_cnt != 0)
    //    n->cost = (double)(contribute - remove)/node_cnt;
    //else
    //    n->cost = 0;

}

//we have pc of rules, tcam of rules, and Graph index of rules.
//the Graph index of rules and tcam of rules should be the same, 
//because this will reduce the operation of Graph rule movement.
//however, after insert a rule into pc, the index of rules stayed below the 
//inserted rule will all be changed ...
//so we would better have a consistency index system of rules. 
//
//Using the rules on the tcam will be easy
//so remember that the rule indexing in pc does not equal to the postion of rules 
//stored in TCAM. 
//
//


void del_rule(tcam & tmap, vector<pc_rule*> &pc, pc_rule *r)
{
    struct node *n  = r->n;

    for(size_t i = 0; i < n->in.size(); i++) {
        auto parent = n->in[i];
        if(parent->out[0] == n) {
            parent->out.erase(parent->out.begin());
            parent->move = -1;
            dfs(parent);
            //compute_cost(parent);
        }
        else {
            auto tail = remove_if(parent->out.begin(), parent->out.end(), [n](struct node *outn){return outn == n;});
            parent->out.erase(tail, parent->out.end());
        }
    }

    for(size_t i = 0; i < n->out.size(); i++) {
        auto child = n->out[i];
        auto tail = remove_if(child->in.begin(), child->in.end(), [n](struct node *inn) {return inn == n;});
        child->in.erase(tail, child->in.end());
        
    }
    
    tmap.del(n->index);
    
    n->in.clear();
    n->out.clear();
    n->index = -1;
    n->move = -1;
    n->cost = -1;
    n->r = nullptr; 
    n->valid = false;

    //pc.erase(pc.begin() + pos);
    auto tail =  remove_if(pc.begin(), pc.end(), [r](const struct pc_rule *rule){return  r == rule;});
    pc.erase(tail, pc.end());
}

void updfs(struct node *n) 
{
    for(size_t i = 0; i < n->in.size(); i++) {
        struct node *p = n->in[i];
        if(p->out[0] == n) {
            updfs(p);
        }
    }

    dfs(n);
}

void udfs(struct node *n) 
{
    n->move = -1;
    for(size_t i = 0; i < n->in.size(); i++) {
       struct node *p = n->in[i];
       if(p->out[0] == n) {
           udfs(p);
       }
    }

    dfs(n);
    //compute_cost(n);
}


//Graph add is handling when acutally the node has been added into G array
void Graph_add(tcam & tmap, pc_rule *r, vector<struct node *> &G, int pos) 
{
    list<struct node *> update;

    for(int i = 0; i < pos; i++) {
        if(overlap(&tmap.pc[i], r)) {
            
            for(size_t j = 0; j < G[i]->out.size(); j++) {
                if(pos < (G[i]->out[j])->index) {
                    G[i]->out.insert(G[i]->out.begin() + j, r->n);
                }
            }

            if(G[i]->out.size() == 0 || G[i]->out[G[i]->out.size()-1]->index < pos) {
                G[i]->out.push_back(r->n);
            }

            r->n->in.push_back(G[i]);

            if(G[i]->out[0] == r->n)
                update.push_back(G[i]);
        }
    }


    for(size_t i = pos+1; i < G.size(); i++) {
        if(overlap(&tmap.pc[i], r)) {
            r->n->out.push_back(G[i]);
            G[i]->in.push_back(r->n);
        }
    }

    for(auto n = update.begin(); n != update.end(); n ++) {
        udfs(*n);
    }

    //if no nodes need to update, we should at least update the r.n
    if(update.size() == 0) {
        dfs(r->n);
    }

}

bool lazy_check(tcam &tmap, pc_rule *r, int pos, vector<pc_rule*> &pc, vector<struct node*> &G)
{
    //up node
    struct node * un = NULL;
    //down node
    struct node * dn = NULL;
    int upos = 0;
    int dpos = 0;

    for(int i = pos-1; i >=0 ; i--) {
        if(overlap(pc[i], r)) {
            un = pc[i]->n;
            break;
        }
    }

    if(un == NULL) {
        upos = pos;
    }
    else{
        upos = un->index +1;
    }
    
    for(size_t i = pos; i < pc.size(); i++) {
        if(overlap(pc[i], r)){
            dn = pc[i]->n;
            break;
        }
    }

    if(dn == NULL) {
        dpos = pc.size(); 
    }
    else {
        dpos = dn->index;
    }

    for(int i = upos; i < dpos; i++) {
        if(tmap.valid[i] == false) {
            //update rule
            r->priority = i;
            //update tcam
            tmap.pc[i] = *r;
            tmap.valid[i] = true;
            //update pc
            pc.insert(pc.begin() + pos, r);
            //update graph
            G[i] = r->n;
            G[i]->r = pc[pos];
            Graph_add(tmap, r, G, i);
            

            return true;
        }
    }
    return false;
}


void tcam_insert(tcam & tmap, vector<struct node*> &G, pc_rule *r, int pos, vector<pc_rule*> &pc) 
{
    struct node *sn = NULL;
    struct node *wn = r->n;
    pc_rule sr; 
    pc_rule wr = *r;

    int insert_pos = -1;
    for(size_t i = pos; i< pc.size(); i++) {
        if(overlap(pc[i], r)) {
            insert_pos = pc[i]->n->index;
            break;
        }
    }
    int first_pos = insert_pos;

    while(insert_pos != -1) {

        sn = G[insert_pos];
        sr = tmap.pc[insert_pos];

        //update rule
        wr.priority = insert_pos;
        //update Graph
        G[insert_pos] = wn;
        G[insert_pos]->index = insert_pos;
        //update tcam
        tmap.pc[insert_pos] = wr;

        wn = sn;
        wr = sr;

        if(sn->out.size() > 0) {
            insert_pos = sn->out[0]->index;
        }
        else {
            insert_pos = -1;
        }
    }

    //update rule
    wr.priority = G.size() - 1;
    //update Graph
    G.push_back(wn);
    G[G.size() -1]->index = G.size() - 1;
    //update tcam
    tmap.pc.push_back(wr);
    tmap.valid.push_back(true);

    if(first_pos == -1)
        first_pos = G.size() - 1;


    Graph_add(tmap, r, G, first_pos);
}


void add_rule(tcam & tmap, vector<struct node*> &G, pc_rule *r, int pos, vector<pc_rule*> &pc)
{
    //first add the node in the tcam, perform movement
    //then update the graph.
    
    r->n = new node();
    //first lazy check
    
    if(!lazy_check(tmap, r, pos, pc, G)) {
        tcam_insert(tmap, G, r, pos, pc); 
    }

    pc.insert(pc.begin() + pos, r);
    r->n->r = pc[pos];
}



void measure(vector<struct node*> &G) 
{
    vector<struct node*> root;

    for(size_t i = 0; i< G.size() ;  i++) {
        if(G[i]->out.size() == 0 && G[i]->valid) {
            G[i]->move = 1;
        }
        if(G[i]->in.size() == 0 && G[i]->valid) {
            root.push_back(G[i]);
        }
    }

    for(size_t i = 0; i < root.size(); i++) {
        dfs(root[i]);
    }
    for(size_t i = 0; i< G.size(); i++) {
        if(G[i]->move == -1 && G[i]->valid)
            updfs(G[i]);
    }
    
    //compute avearage move
    int sum = 0;
    int max_move = 0;
    int valid_cnt = 0;
    for(size_t i = 0; i < G.size(); i++) {
        if(G[i]->valid == true) {
            sum += G[i]->move;
            if(G[i]->move > max_move)
                max_move = G[i]->move;
            valid_cnt ++;
        }
    }
    cout <<"max move "<<max_move<<endl;
    cout <<"average move "<<(double)sum/valid_cnt<<endl;


    //compute cost
    //double max_cost = 0;
    //double min_cost = 0xffffff;
    //for(size_t i = 0; i < G.size(); i++) {
    //    //compute_cost(G[i]);
    //    if(G[i]->cost > max_cost) {
    //        max_cost = G[i]->cost;
    //    }
    //    if(G[i]->cost < min_cost) {
    //        min_cost = G[i]->cost;
    //    }
    //    //cout<<"cost "<<G[i].cost<<endl;
    //}


    //cout<<"cost "<<max_cost<<" "<<min_cost<<endl;
}

void measure_avgmove(vector<struct node*> &G, double &avg_move_r, int &max_move_r) 
{
    int sum =0;
    int max_move = 0;
    int valid_cnt = 0;

    for(size_t i = 0; i< G.size(); i++) {
        if(G[i]->valid == true) {
            sum += G[i]->move;
            valid_cnt ++;
            if(G[i]->move > max_move) 
                max_move = G[i]->move;
        }
    }
    cout<<"sum move "<<sum<<endl;
    cout<<"max move "<<max_move<<endl;

    avg_move_r = (double)sum/valid_cnt;
    max_move_r = max_move;
    cout<<"avg move "<<avg_move_r<<endl;
}

//vector<vector<pc_rule*> > split_ruleset_bound(vector<struct node*> &G, vector<pc_rule*> &pc, int bound, tcam & tmap) 
//{
//    vector<struct node*> root; 
//    for(size_t i = 0; i < G.size(); i++) {
//        if(G[i]->in.size() == 0) {
//            G[i]->type = ROOT;
//            root.push_back(G[i]);
//        }
//    }
//
//    for(size_t i = 0; i< root.size(); i++) {
//
//    }
//
//}

//vector<vector<pc_rule*> >  split_ruleset_cost(vector<struct node*> &G, vector<pc_rule*> &pc, int num_threshold, tcam & tmap)
//{
//    vector<struct node*> SG = G;
//    vector<vector<pc_rule*> > ret;
//
//    vector<pc_rule*> sub;
//    sort(SG.begin(), SG.end(), [](struct node *n1, struct node* n2) { return n1->cost > n2->cost;});
//    
//    int i = 0;
//    for(; i < num_threshold; i++) {
//        struct node * nd = SG[0];
//        SG.erase(SG.begin());
//        sub.push_back(nd->r);
//        del_rule(tmap, pc, nd->r);
//        sort(SG.begin(), SG.end(), [](struct node *n1, struct node* n2) { return n1->cost > n2->cost;});
//    }
//
//    sort(sub.begin(), sub.end(), [](pc_rule *r1, pc_rule *r2) {return r1->priority <  r2->priority;});
//    //double avg_move_r;
//    //int max_move_r;
//    //measure_avgmove(G, avg_move_r, max_move_r);
//
//
//    cout<<"sub ruleset "<<sub.size()<<endl;
//    vector<struct node *> G2;
//    build_graph(sub,G2); 
//    measure(G2);
//    return vector<vector<pc_rule*> >();
//    
//}


vector<pc_rule*> remove_redund_pkg(vector<pc_rule> &pc, vector<pc_rule> &pc_prefix) 
{
    rule_boundary rb;
    init_boundary(rb);
    
    //pc_prefix = pc;
    
    vector<pc_rule*> pcr;
    for_each(pc.begin(), pc.end(), [&pcr](pc_rule &r){pcr.push_back(&r);});
    cout<<"Orignal ruleset "<<pc.size()<<endl;

    remove_redund_rt(pcr, rb, false);
    extend_rules(pcr, pc_prefix);
    
    cout<<"After prefix explanation: "<< pc_prefix.size()<<endl;

    vector<pc_rule*> pc_pprefix;
    for_each(pc_prefix.begin(), pc_prefix.end(), [&pc_pprefix](pc_rule &r){pc_pprefix.push_back(&r);});


    
    for(int i = 0; i< (int)pcr.size();i ++) {
        pc_pprefix[i]->priority = i;
    }

    return move(pc_pprefix);

}



void print_path(struct node *n) 
{
    struct node *curr = n;
    while(curr->out.size() != 0) {
        cout<<curr->r->priority<< " - ";
        curr = curr->out[0];
    }

    cout<<endl;
}

void print_long_paths(vector<struct node*> &G, int length_path) 
{
    for(size_t i = 0; i < G.size(); i++) {
        if(G[i]->valid && G[i]->move > length_path) {
            print_path(G[i]);
        }
    }
}

//bool label_flags = false;

void print_out_degree(vector<struct node *> &G)
{
    for(size_t i = 0; i< G.size(); i++) {
        if(G[i]->valid) {
            cout<<G[i]->out.size()<<endl;
        }
    }
}

int label_node(struct node *n) 
{
    if(n->in.size() == 0) {
        n->label = 0;
    }

    if(n->label == -1) {
        int zcnt = 0;
        int ocnt = 0;
        for(size_t i = 0; i < n->in.size(); i++) {
            if(label_node(n->in[i]) == 0) {
                zcnt ++;
            }

            if(label_node(n->in[i]) == 1) {
                ocnt ++;
            }
        }
        n->label = (zcnt > ocnt) ? 1 : 0;
        //if (zcnt > ocnt) {
        //    n->label = 1;
        //}
        //else if (zcnt < ocnt) {
        //    n->label = 0;
        //}
        //else {
        //    n->label = (label_flags == true) ? 1: 0;
        //    label_flags = !label_flags;
        //}
    }
    return n->label;
}

void zo_split(vector<struct node *> &G, vector<struct node *> &subG1, vector<struct node *> &subG2)
{
    cout << endl;
    cout << "0 - 1 split" <<endl;
    for(size_t i = 0; i< G.size(); i++) {
        label_node(G[i]);
    }

    vector<pc_rule*> pc_0;
    vector<pc_rule*> pc_1;

    for(size_t i = 0; i < G.size(); i++) {
        if(G[i]->label == 0) {
            pc_0.push_back(G[i]->r);
        }
        if(G[i]->label == 1) {
            pc_1.push_back(G[i]->r);
        }
    }

    vector<struct node *> G0;
    vector<struct node *> G1;

    cout<<"split sets 0 " << pc_0.size()<<endl;
    build_graph(pc_0, G0);
    measure(G0);
    cout<<"split sets 1 " << pc_1.size()<<endl;
    build_graph(pc_1, G1);
    measure(G1);


    subG1 = move(G0);
    subG2 = move(G1);
}

void filtering_largerules(vector<pc_rule*> &in, vector<pc_rule*> &out, vector<pc_rule*> * filtering_out) 
{
    for(auto rule = in.begin(); rule != in.end(); rule++) {
        if(check_range_size((*rule)->field[0], 0) && check_range_size((*rule)->field[1], 1)) {
            if(filtering_out) {
                filtering_out->push_back(*rule);
            }
            continue;
        }
        out.push_back(*rule);
    }

}

void hybrid_arch(vector<pc_rule*> &in)
{
    cout<<endl<<"Hybrid arch" <<endl;
    vector<pc_rule*> filtering;
    vector<pc_rule*> out;
    filtering_largerules(in, out, &filtering);
    cout<<"filtering "<<filtering.size()<<endl;


    vector<struct node*> G;
    vector<struct node*> G2;

    cout<<endl<<"******before******"<<endl;
    build_graph(in, G);
    measure(G);

    cout<<endl<<"*****after******"<<endl;
    build_graph(out, G2);
    measure(G2);

    cout<<endl<<"Split "<<endl;
    vector<struct node *> subG1;
    vector<struct node *> subG2;

    vector<struct node *> subG3;
    vector<struct node *> subG4;

    zo_split(G2, subG1, subG2);
    zo_split(subG2, subG3, subG4);


}

void pure_arch(vector<pc_rule*> &in) 
{
    cout<<endl<<"Pure Arch"<<endl;
    vector<struct node *> G2;
    build_graph(in, G2);


    vector<struct node *> subG1;
    vector<struct node *> subG2;

    vector<struct node *> subG3;
    vector<struct node *> subG4;

    zo_split(G2, subG1, subG2);
    zo_split(subG2, subG3, subG4);

}




int main(int argc, char *argv[])
{

    vector<pc_rule> pc_orig;
    vector<pc_rule> pc_prefix;
    vector<pc_rule*> pc;

    parseargs(argc, argv);
    loadrules(fpr, pc_orig);

    vector<pc_rule*> pc_r = remove_redund_pkg(pc_orig, pc_prefix);
    cout<<"load "<<pc_r.size()<<" rules"<<endl;

    pure_arch(pc_r); 
    hybrid_arch(pc_r);

    //tcam tmap;
    //vector<struct node*> G;
    //for(size_t i = 0; i < pc_r.size(); i++) {
    //    //if(i == 780)
    //    //   cout<<"here"<<endl;
    //    add_rule(tmap, G, pc_r[i], i, pc);
    //}

    //double avg_move;
    //int max_move;
    //measure_avgmove(G, avg_move, max_move);
    //cout<<endl;
    //cout<<"avg move "<<avg_move<<endl;
    //cout<<"max move "<<max_move<<endl;
    //print_long_paths(G, 10);
    //print_out_degree(G);
    //measure(G);



    //split_ruleset_cost(G, pc, pc.size()/2, tmap);
    //for(size_t i = 0; i< G.size(); i++) {
    //measure_avgmove(G, avg_move, max_move);
    //    if(G[i]->in.size() == G2[i]->in.size() &&
    //            G[i]->out.size() == G2[i]->out.size()
    //            && G[i]->move == G2[i]->move) {

    //        continue;
    //    }i
    //    else {
    //        cout << "error"<< i <<endl;
    //    }
    //}

        //print_out_degree(subG3);
    //print_out_degree(subG2);
    //print_long_paths(subG3, 10);

    return 0;
}

