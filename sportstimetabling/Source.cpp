#include<iostream>
#include<vector>
#include<string>
#include "tinyxml2.h"
#include <ilcplex/ilocplex.h>
using namespace std;
using namespace tinyxml2;

vector<int> stov(const char* s)
{
	//convert string of type "a1;a2;a3;a4;a5" to vector {a1,a2,a3,a4,a4,a5}
	vector<int>ans;
	int it = 0;
	while (s[it] != '\0')
	{
		int a = (int)(s[it] - '0');
		it++;
		while (s[it] != '\0' && s[it] != ';')
		{
			int b = (int)(s[it] - '0');
			a = 10 * a + b;
			it++;
		}
		ans.push_back(a);
		if (s[it] == ';')
			it++;
	}
	return ans;
}
vector<pair<int, int>>stov2(const char* m)
{
	//convert string(of type "a1,b1;a2,b2;a3,b3") to vector{{a1,b1},{a2,b2},{a3,b3}} 
	vector<pair<int, int>>ans;
	int i = 0;
	while (m[i] != '\0')
	{
		pair<int, int>p;
		int a = (int)(m[i] - '0');
		i++;
		while (m[i] != '\0' && m[i] != ',')
		{
			int at = (int)(m[i] - '0');
			a = 10 * a + at;
			i++;
		}
		//m[i]==','
		i++;
		int b = (int)(m[i] - '0');
		i++;
		while (m[i] != '\0' && m[i] != ';')
		{
			int bt = (int)(m[i] - '0');
			b = 10 * b + bt;
			i++;
		}
		p.first = a;
		p.second = b;
		ans.push_back(p);
		if(m[i]==';')
		i++;
	}
	return ans;
}
int main()
{
	IloEnv env;
	try {
		XMLDocument doc;
		doc.LoadFile("ITC2021_Test4.xml");
		
		XMLElement* root = doc.RootElement();	
		IloInt  n = 0;
		if (root)
		{
			XMLElement* teams = root->FirstChildElement("Resources")->FirstChildElement("Teams");
			if (teams)
			{
				XMLElement* team = teams->FirstChildElement("team");
				while (team)
				{
					n++;
					team = team->NextSiblingElement("team");
				}
				cout << "n=" << n << '\n';
			}
			else
			{
				cerr << "Error: Teams not found\n";
			}
		}
		else
		{
			cerr << "Error :Unable to Load xml file"<<"\n";
		}
		//declaring decision variables x[i][j][k] as binary variables 
		IloArray<IloArray<IloNumVarArray>>  x(env, n);
		//d == deviations for soft constraint
		IloNumVarArray d(env);
		//y ==binary variables for separation constraint  
		IloNumVarArray y(env);
		//preprocessing for break constraints
		IloArray<IloNumVarArray>h(env, n);
		IloArray<IloNumVarArray>a(env, n);
	
		//penalties for soft constraint
		vector<int>penalties;
		for (int i = 0; i < n; i++)
		{
			x[i] = IloArray<IloNumVarArray>(env, n);
			for (int j = 0; j < n; j++)
			{
				x[i][j] = IloNumVarArray(env, 2 * (n - 1));
				for (int k = 0; k < 2 *(n - 1); k++)
				{
					x[i][j][k] = IloNumVar(env, 0.0, 1.0, ILOINT);
				}
			}
		}
		IloModel model(env);
		//basic constraint 1: x[i][i][k] =0 for every i,k
		//(No team plays against self)
		for (int i = 0; i < n; i++)
		{
			for (int k = 0; k < 2 * (n - 1); k++)
			{
				model.add(x[i][i][k] == 0);
			}
		}
		//basic constraint 2: sum over j (x[i][j][k]+x[j][i][k] )==1 for every i,k
		//(each team play exactly one game in each slot)
		for (int i = 0; i < n; i++)
		{
			
			for (int k = 0; k < 2 * (n - 1); k++)
			{
				IloExpr c(env);
				for (int j = 0; j < n; j++)
				{
					c += x[i][j][k];
					c += x[j][i][k];
				}
				model.add(c == 1);
				c.end();
			}
		}
		//basic constraint 3: sumover k,j(x[i][j][k]) == n-1 for every i
		//Every team plays n-1 home games
		for (int i = 0; i < n; i++)
		{
			IloExpr c(env);
			for (int j = 0; j < n; j++)
			{
				for (int k = 0; k < 2 * (n - 1); k++)
				{
					c += x[i][j][k];
				}
			}
			model.add(c == n - 1);
			c.end();
		}
		//basic constraint 4: sum over k(x[i][j][k]) ==1 for every i,j ,i!=j
		//(every team play 1 home and 1 away game against each other)
		for (int i = 0; i < n; i++)
		{
			for (int j = 0; j < n; j++)
			{
				if (i == j)
				{
					continue;
				}
				else
				{
					IloExpr c(env);
					for (int k = 0; k < 2 * (n - 1); k++)
					{
						c += x[i][j][k];
					}
					model.add(c == 1);
					c.end();
				}
			}
		}
		if (root)
		{
			XMLElement* mode = root->FirstChildElement("Structure")->FirstChildElement("Format")->FirstChildElement("gameMode");
			if (mode)
			{
				
				if ((mode->GetText())[0] == 'P')
				{
					//phased constraint holds true
					//each team play every other team exactly once in first half of the tournament
					//sum over k =1 to k =n-1 (x[i][j][k]+x[j][i][k]) ==1 for evry i,j i!=j
					for (int i = 0; i < n; i++)
					{
						for (int j = i + 1; j < n; j++)
						{
							IloExpr c(env);
							for (int k = 0; k < n - 1; k++)
							{
								c += x[i][j][k];
								c += x[j][i][k];

							}
							model.add(c == 1);
							c.end();
						}
					}
				}
			}
			else
			{
				cerr << "error: gamemode not found\n";
			}
		}
		
		for (int i = 0; i < n; i++)
		{
			h[i] = IloNumVarArray(env, 2 * (n - 1));
			a[i] = IloNumVarArray(env, 2 * (n - 1));
			h[i][0] = IloNumVar(env, 0.0, 0.0, ILOINT);
			a[i][0] = IloNumVar(env, 0.0, 0.0, ILOINT);
			for (IloInt k = 1; k < 2 * (n - 1); k++)
			{
				h[i][k] = IloNumVar(env, 0.0, 1.0, ILOINT);
				a[i][k] = IloNumVar(env, 0.0, 1.0, ILOINT);
				IloExpr hc(env), ac(env);
				//h[i][k]==1 if there is  a home break for team i in kth slot
				//a[i][k]==1 if there is  an away break for team i in kth slot
				//h[i][k]== sumover all j(x[i][j][k-1])*sumover all j(x[i][j][k])
				//a[i][k]== sumover all j(x[j[i[k-1])*sumover all j(x[j][i[k])
				//it can be written as :
				//sumover all j(x[i][j][k-1])+sumover all j(x[i][j][k]) -1 <= h[i][k]
				//sumover all j(x[j][i][k-1])+sumover all j(x[j][i][k]) -1 <= a[i][k]
				for (int j = 0; j < n; j++)
				{
					hc += x[i][j][k-1]+ x[i][j][k];
					ac += x[j][i][k-1]+ x[j][i][k];
				}
				model.add(hc - 1 <= h[i][k]);
				model.add(ac - 1 <= a[i][k]);
				ac.end();
				hc.end();
			}
		}
		if (root)
		{
			XMLElement * constraints = root->FirstChildElement("Constraints");
			if (constraints)
			{
				XMLElement * capacityc = constraints->FirstChildElement("CapacityConstraints");
				XMLElement * gamec = constraints->FirstChildElement("GameConstraints");
				XMLElement * breakc = constraints->FirstChildElement("BreakConstraints");
				XMLElement * fairnessc = constraints->FirstChildElement("FairnessConstraints");
				XMLElement * separationc = constraints->FirstChildElement("SeparationConstraints");
				
				if(capacityc)    
				{
					XMLElement* ca1 = capacityc->FirstChildElement("CA1");
					while (ca1)
					{
						const char* type = ca1->Attribute("type");
						int team,min,max;
						int penalty;
						const char* s = ca1->Attribute("slots");
						const char* mode = ca1->Attribute("mode");
						vector<int> slots =stov(s);					
						ca1->QueryAttribute("teams", &team);
						ca1->QueryAttribute("penalty", &penalty);
						ca1->QueryAttribute("min", &min);
						ca1->QueryAttribute("max", &max);
						IloExpr c(env);
						for (int j = 0; j < n; j++)
						{
							
							for (int k = 0; k < slots.size(); k++)
							{
								if (mode[0] == 'H')
								{
									c += x[team][j][slots[k]];
								}
								else if (mode[0] == 'A')
								{
									c += x[j][team][slots[k]];
								}
							}
							
						}
						if (type[0] == 'H')
						{
							//Hard constraint
							model.add(c <= max);
							model.add(c >= min);
							c.end();
						}
						else if (type[0] == 'S')
						{
							//soft constraint
							d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
							penalties.push_back(penalty);
							model.add(c - d[d.getSize() - 1] <= max);
							c.end();
						}

						ca1 = ca1->NextSiblingElement("CA1");
					}
					XMLElement* ca2 = capacityc->FirstChildElement("CA2");
					while (ca2)
					{
						const char* type = ca2->Attribute("type");
						int team1, min, max;
						int penalty;
						const char* s = ca2->Attribute("slots");
						const char* mode = ca2->Attribute("mode1");
						const char* t2 = ca2->Attribute("teams2");
						vector<int>teams2 =stov(t2);
						vector<int> slots=stov(s);
						
						ca2->QueryAttribute("teams1", &team1);
						ca2->QueryAttribute("penalty", &penalty);
						ca2->QueryAttribute("min", &min);
						ca2->QueryAttribute("max", &max);
						IloExpr c(env);
						for (int j = 0; j < teams2.size(); j++)
						{
							
							for (int k = 0; k < slots.size(); k++)
							{
								if (mode[0] == 'H'&& mode[1]=='\0')
								{
									c += x[team1][teams2[j]][slots[k]];
								}
								else if (mode[0] == 'A')
								{
									c += x[teams2[j]][team1][slots[k]];
								}
								else if (mode[0] == 'H' && mode[1] == 'A')
								{
									if (slots.size() == 6 && team1 == 1 && teams2.size() == 3)
									{
										cout <<slots[k];
									}
									c += x[teams2[j]][team1][slots[k]] + x[team1][teams2[j]][slots[k]];
								}

							}
							
						}
						if (type[0] == 'H')
						{
							//Hard constraint
							model.add(c <= max);
							model.add(c >= min);
							c.end();
						}
						else if (type[0] == 'S')
						{
							//soft constraint
							d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
							penalties.push_back(penalty);
							model.add(c - d[d.getSize() - 1] <= max);
							c.end();
						}
						ca2 = ca2->NextSiblingElement("CA2");
					}
					XMLElement* ca3 = capacityc->FirstChildElement("CA3");
					while (ca3)
					{
						const char* type = ca3->Attribute("type");
						int  min, max,intp;
						int penalty;
						const char* t1 = ca3->Attribute("teams1");
						const char* t2 = ca3->Attribute("teams2");
						const char* mode = ca3->Attribute("mode1");
						vector<int> teams2 = stov(t2);
						vector<int> teams1 = stov(t1);
						
						ca3->QueryAttribute("penalty", &penalty);
						ca3->QueryAttribute("min", &min);
						ca3->QueryAttribute("max", &max);
						ca3->QueryAttribute("intp", &intp);
						for (int i = 0; i < teams1.size(); i++)
						{
							
							for (int l = 0; l <= 2*(n-1) - intp; l++)
							{
								IloExpr c(env);
								for (int j = 0; j < teams2.size(); j++)
								{
									for (int k = l; k < l + intp; k++)
									{
										if (mode[0] == 'H' && mode[1] == '\0')
										{
											c += x[teams1[i]][teams2[j]][k];
										}
										else if (mode[0] == 'A')
										{
											c += x[teams2[j]][teams1[i]][k];
											
										}
										else if (mode[0] == 'H' && mode[1] == 'A')
										{
											c += x[teams2[j]][teams1[i]][k] + x[teams1[i]][teams2[j]][k];
										}
									}
									
								}
								if (type[0] == 'H')
								{
									//Hard constraint
									model.add(c <= max);
									model.add(c >= min);
									c.end();
								}
								else if (type[0] == 'S')
								{
									//soft constraint
									d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
									penalties.push_back(penalty);
									model.add(c - d[d.getSize() - 1] <= max);
									c.end();
								}
							}
						}
						ca3 = ca3->NextSiblingElement("CA3");
					}
					XMLElement* ca4 = capacityc->FirstChildElement("CA4");
					while (ca4)
					{
						const char* type = ca4->Attribute("type");
						int  min, max;
						int penalty;
						const char* t1 = ca4->Attribute("teams1");
						const char* t2 = ca4->Attribute("teams2");
						const char* s = ca4->Attribute("slots");
						const char* mode1 = ca4->Attribute("mode1");
						const char* mode2 = ca4->Attribute("mode2");
						vector<int>teams1 = stov(t1);
						vector<int> teams2 = stov(t2);
						vector<int>slots = stov(s);
						ca4->QueryAttribute("penalty", &penalty);
						ca4->QueryAttribute("min", &min);
						ca4->QueryAttribute("max", &max);
						if (mode2[0] == 'G')
						{
							//mode2 =global
							IloExpr c(env);
							for (int i = 0; i < teams1.size(); i++)
							{
								for (int j = 0; j < teams2.size(); j++)
								{
									for (int k = 0; k < slots.size(); k++)
									{
										if (mode1[0] == 'H' && mode1[1] == '\0')
										{
											c += x[teams1[i]][teams2[j]][slots[k]];
										}
										else if (mode1[0] == 'A')
										{
											c += x[teams2[j]][teams1[i]][slots[k]];
										}
										else if (mode1[0] == 'H' && mode1[1] == 'A')
										{
											c += x[teams2[j]][teams1[i]][slots[k]] + x[teams1[i]][teams2[j]][slots[k]];
										}
									}
								}
							}
							if (type[0] == 'H')
							{
								//Hard constraint
								model.add(c <= max);
								model.add(c >= min);
								c.end();
							}
							else if (type[0] == 'S')
							{
								//soft constraint
								d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
								penalties.push_back(penalty);
								model.add(c - d[d.getSize() - 1] <= max);
								c.end();
							}
						}
						else if (mode2[0] == 'E')
						{
							//mode2=every
							for (int k = 0; k < slots.size(); k++)
							{
								IloExpr c(env);
								for (int i = 0; i < teams1.size(); i++)
								{
									for (int j = 0; j < teams2.size(); j++)
									{
										if (mode1[0] == 'H' && mode1[1] == '\0')
										{
											c += x[teams1[i]][teams2[j]][slots[k]];
										}
										else if (mode1[0] == 'A')
										{
											c += x[teams2[j]][teams1[i]][slots[k]];
										}
										else if (mode1[0] == 'H' && mode1[1] == 'A')
										{
											c += x[teams2[j]][teams1[i]][slots[k]] + x[teams1[i]][teams2[j]][slots[k]];
										}
									}
								}
								if (type[0] == 'H')
								{
									//Hard constraint
									model.add(c <= max);
									model.add(c >= min);
									c.end();
								}
								else if (type[0] == 'S')
								{
									//soft constraint
									d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
									penalties.push_back(penalty);
									model.add(c - d[d.getSize() - 1] <= max);
									c.end();
								}
							}
						}
						ca4 = ca4->NextSiblingElement("CA4");
					}
				}
				else
				{
					cerr << "error:capacity constraints not found\n";
				}

				if (gamec)
				{
					XMLElement* ga1 = gamec->FirstChildElement("GA1");
					while (ga1)
					{
						const char* type = ga1->Attribute("type");
						int  min, max;
						int penalty;
						
						const char* s = ga1->Attribute("slots");
						const char* m = ga1->Attribute("meetings");
						vector<pair<int, int>>meetings =stov2(m);
						vector<int>slots = stov(s);
						ga1->QueryAttribute("penalty", &penalty);
						ga1->QueryAttribute("min", &min);
						ga1->QueryAttribute("max", &max);
						IloExpr c(env);
						for (int i = 0; i < meetings.size(); i++)
						{
							for (int k = 0; k < slots.size(); k++)
							{
								c += x[meetings[i].first][meetings[i].second][slots[k]];
							}
						}
						if (type[0] == 'H')
						{
							//hard constraint
							model.add(c <= max);
							model.add(c >= min);
							c.end();
						}
						else if (type[0] == 'S')
						{
							//soft constraint
							d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
							penalties.push_back(penalty);
							model.add(c - d[d.getSize() - 1] <= max);
							model.add(d[d.getSize() - 1] + c >= min);
							c.end();
						}
						ga1 = ga1->NextSiblingElement("GA1");
					}
				}
				else
				{
					cerr << "error:game constraints not found\n";
				}

				if (breakc)
				{
					XMLElement* br1 = breakc->FirstChildElement("BR1");
					while (br1)
					{
						const char* type = br1->Attribute("type");
						int  team,intp;
						int penalty;
						const char* s = br1->Attribute("slots");
						const char* mode = br1->Attribute("mode2");
						vector<int>slots = stov(s);
						br1->QueryAttribute("penalty", &penalty);
						br1->QueryAttribute("teams", &team);
						br1->QueryAttribute("intp", &intp);
						IloExpr c(env);
						for (int k = 0; k < slots.size(); k++)
						{
								
							if (mode[0] == 'H'&&mode[1]=='\0')
							{
								c += h[team][slots[k]];
							}
							else if (mode[0] == 'A')
							{
								c += a[team][slots[k]];
							}
							else if (mode[0] == 'H' && mode[1] == 'A')
							{
								c += h[team][slots[k]] + a[team][slots[k]];
							}
						}
						if (type[0] == 'H')
						{
							//Hard constraint
							model.add(c <= intp);
							c.end();
						}
						else if (type[0] == 'S')
						{
							//soft constraint
							d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
							penalties.push_back(penalty);
							model.add(c - d[d.getSize() - 1] <= intp);
							c.end();
						}
						
						br1 = br1->NextSiblingElement("BR1");
					}
					XMLElement* br2 = breakc->FirstChildElement("BR2");
					while (br2)
					{
						const char* type = br2->Attribute("type");
						int   intp;
						int penalty;
						const char* s = br2->Attribute("slots");
						const char* mode = br2->Attribute("homeMode");
						const char* t = br2->Attribute("teams");
						vector<int>slots = stov(s);
						vector<int>teams = stov(t);
						br2->QueryAttribute("penalty", &penalty);
						br2->QueryAttribute("intp", &intp);
						IloExpr c(env);
						for (int i = 0; i < teams.size(); i++)
						{
							for (int k = 0; k < slots.size(); k++)
							{
								if (mode[0] == 'H' && mode[1] == '\0')
								{
									c += h[teams[i]][slots[k]];
								}
								else if (mode[0] == 'A')
								{
									c += a[teams[i]][slots[k]];
								}else if (mode[0] == 'H' && mode[1] == 'A')
								{
									c += h[teams[i]][slots[k]] + a[teams[i]][slots[k]];
								}
							}
						}
						if (type[0] == 'H')
						{
							//Hard constraint
							model.add(c <= intp);
							c.end();
						}
						else if (type[0] == 'S')
						{
							//soft constraint
							d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
							penalties.push_back(penalty);
							model.add(c - d[d.getSize() - 1] <= intp);
							c.end();
						}
						br2 = br2->NextSiblingElement("BR2");
					}
				}
				else
				{
					cerr << "error:break constraints not found\n";
				}

				if (fairnessc)
				{
					XMLElement* fa2 = fairnessc->FirstChildElement("FA2");
					while (fa2)
					{
						const char* type = fa2->Attribute("type");
						int   intp;
						int penalty;
						const char* s = fa2->Attribute("slots");
						const char* mode = fa2->Attribute("mode");
						const char* t = fa2->Attribute("teams");
						vector<int>slots = stov(s);
						vector<int>teams = stov(t);
						fa2->QueryAttribute("penalty", &penalty);
						fa2->QueryAttribute("intp", &intp);
						for (int i = 0; i < teams.size(); i++)
						{
							for (int j = i + 1; j < teams.size(); j++)
							{
								for (int k = 0; k < slots.size(); k++)
								{
									IloExpr c(env);
									for (int k2 = 0; k2 <= k; k2++)
									{
										for (int j2 = 0; j2 < n; j2++)
										{
											if (mode[0] == 'H' && mode[1] == '\0')
											{
												c += x[teams[i]][j2][k2];
												c -= x[teams[j]][j2][k2];
											}
										}
									}
									if (type[0] == 'H')
									{
										//Hard constraint
										model.add(c <= intp);
										model.add(c >= -intp);
										c.end();
									}
									else if (type[0] == 'S')
									{
										//soft constraint
										d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
										penalties.push_back(penalty);
										model.add(c - d[d.getSize() - 1] <= intp);
										model.add(c + d[d.getSize() - 1] >= -intp);
										c.end();
									}
								}
							}
						}
						fa2 = fairnessc->NextSiblingElement("FA2");
					}
				}
				else
				{
					cerr << "error:fairness constraints not found\n";
				}

				if (separationc)
				{
					XMLElement* se1 = separationc->FirstChildElement("SE1");
					while (se1)
					{
						const char* type = se1->Attribute("type");
						int   min;
						int penalty;
						
						
						const char* t = se1->Attribute("teams");
						
						vector<int>teams = stov(t);
						se1->QueryAttribute("penalty", &penalty);
						se1->QueryAttribute("min", &min);
						min++;
						for (int i = 0; i < teams.size(); i++)
						{
							for (int j = i+1; j < teams.size(); j++)
							{
								IloExpr c(env);
								for (int k = 0; k < 2 * (n - 1); k++)
								{
									c += k*x[teams[i]][teams[j]][k];
									c -= k*x[teams[j]][teams[i]][k];
								}
								//c== s2-s1 ,where s2 = slot for match (teams[i],teams[j]) & s1= slot for match(teams[j],teams[i])
								//so we want either c>=min or c<=-(min)
								// y==0 or 1 if either of above two constraints holds true respectively 
								
								if (type[0] == 'H')
								{
									//hard constraint
									//either min<=c or c<=-min
									y.add(IloNumVar(env, 0.0, 1.0, ILOINT));
									model.add(min-c<= INT_MAX * y[y.getSize()-1]);
									model.add(c+min<=INT_MAX*(1- y[y.getSize() - 1]));
									c.end();
								}
								else if (type[0] == 'S')
								{
									//soft constraint
									d.add(IloNumVar(env, 0, IloInfinity, ILOINT));
									penalties.push_back(penalty);
									//if c>0 we want d== min-c or d-min+c>=0
									//instead we will add 2 constraints(if-then)
									//c <=M(1-y) & -(d-min+c)<=M*y
									y.add(IloNumVar(env, 0.0, 1.0, ILOINT));
									model.add( c <= INT_MAX * (1 - y[y.getSize() - 1]));
									model.add(min - d[d.getSize() - 1] - c <= INT_MAX * y[y.getSize()-1]);
									//Also
									//if c<0 or -c>0 then d==c+min=or d-c-min>=0
									//instead we will add 2 constraints(if-then)
									//-c <=M(1-y) & -(d-min-c)<=M*y
									y.add(IloNumVar(env, 0.0, 1.0, ILOINT));
									model.add(-c <= INT_MAX * (1 - y[y.getSize() - 1]));
									model.add(+min - d[d.getSize() - 1] + c <= INT_MAX * y[y.getSize() - 1]);
									c.end();
								}
							}
						}
						se1 = separationc->NextSiblingElement("SE1");
					}
				}
				else
				{
					cerr << "error:separation constraints not found\n";
				}

			}
			else
			{
				cerr << "Error:Constraints not found\n";
			}
		}
		IloExpr obj(env);
		for (int i = 0; i < penalties.size(); i++)
		{
			obj += (d[i] * penalties[i]);
		}
		model.add(IloMinimize(env, obj));
		obj.end();
		IloCplex cplex(env);
		cplex.extract(model);
		cplex.solve();
	/*	cout << "Status: " << cplex.getStatus() << endl;*/
		cout << "Optimal value of objective: " << cplex.getObjValue() << endl;
		XMLDocument doc2;
		const char* fname = "ITC2021_Solution_Test4.xml";
		const char* sname = "ITC2021_Solution_Test4";
		XMLNode* root2 = doc2.NewElement("Solution");
		doc2.InsertFirstChild(root2);
		XMLElement* md = doc2.NewElement("MetaData");
		root2->InsertFirstChild(md);
		XMLElement * in =doc2.NewElement("InstanceName");
		in->SetText(fname);
		md->InsertFirstChild(in);
		XMLElement* sn = doc2.NewElement("SolutionName");
		sn->SetText(sname);
		md->InsertEndChild(sn);
		XMLElement* ov = doc2.NewElement("ObjectiveValue");
		ov->SetAttribute("objective", cplex.getObjValue());
		ov->SetAttribute("infeasibility",0);
		
		md->InsertEndChild(ov);
		XMLElement* game = doc2.NewElement("Games");
		root2->InsertEndChild(game);
		for (int k = 0; k < 2 * (n - 1); k++)
		{
			cout << "Round " << k  << ": ";
			for (int i = 0; i < n; i++)
			{
				for (int j = 0; j < n; j++)
				{
					
					if (cplex.getValue(x[i][j][k]) >= 0.999999)
					{
						cout << "(" << i  << " , " << j  << ") ";
						XMLElement* m = doc2.NewElement("ScheduledMatch");
						m->SetAttribute("home", i);
						m->SetAttribute("away", j);
						m->SetAttribute("slot", k);
						game->InsertEndChild(m);
					}
				}
			}
			
			cout << "\n";
		}
		/*for (int j = 0; j < d.getSize(); j++)
		{
			if (cplex.getValue(d[j]) > 0.0001)
			{
				cout << penalties[j]<<",";
				cout << cplex.getValue(d[j]) << "\n";
			}
		}*/
		doc2.SaveFile(fname);
	}
	catch (IloException& e) {
		cerr << " ERROR: " << e << endl;
		throw;
	}
	catch (...) {
		cerr << " ERROR" << endl;
		throw;
	}
	env.end();
	return 0;
}