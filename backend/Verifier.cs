/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Security;
using System.Transactions;
using System.Xml.Linq;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new ();
        TextWriter writer;
        List<BasicPath> basic_paths = new ();          // 基本路径
        Dictionary<Location, bool> loop_cache = new ();     // 处理循环

        public Verifier ( TextWriter writer )
        {
            this.writer = writer;
        }

        public static Expression Merge_expression ( List<Expression> func )
        {
            Expression tmp;
            int num = func.Count;
            if (num == 0)
            {
                tmp = new BoolConstantExpression ( true );
            }
            else if (num == 1)
            {
                tmp = func [ 0 ];
            }
            else
            {
                tmp = func [0];
                for (int j = 1; j < num; j++)
                {
                    tmp = new AndExpression ( tmp, func [j] );
                }
            }
            return tmp;
        }

        // 复制备用项
        public static BasicPath Copy_path ( BasicPath basicPath )
        {
            BasicPath tmp = new ();
            tmp.headConditions = new List<Expression> ( basicPath.headConditions );
            tmp.headRankingFunctions = new List<Expression> ( basicPath.headRankingFunctions );
            tmp.statements = new List<Statement> ( basicPath.statements );
            tmp.tailConditions = new List<Expression> ( basicPath.tailConditions );
            tmp.tailRankingFunctions = new List<Expression> ( basicPath.tailRankingFunctions );
            return tmp;
        }

        // 遍历后继
        public bool Scan_post ( BasicPath current_path, Location location, List<BasicPath> assumePath )
        {
            List<Statement> statement = location.succStatements;
            int succ_num = location.succStatements.Count;
            bool flag_ = false;

            for (int i = 0; i < succ_num; i++)
            {
                Statement current_statement = statement [ i ];
                if (current_statement is AssertStatement assert)
                {
                    // assert则直接结束
                    current_path.tailConditions.Add ( assert.pred );
                    BasicPath tmp_path = Copy_path ( current_path );
                    basic_paths.Add ( tmp_path );
                }
                // assume
                else if (current_statement is AssumeStatement assume)
                {
                    flag_ = true;
                    BasicPath tmp_path = Copy_path ( current_path );
                    tmp_path.statements.Add ( assume );
                    assumePath.Add ( tmp_path );
                }
                // 内部过程
                else if (current_statement is FunctionCallStatement func)
                {

                    //第一条路径，进入函数                                            
                    List<LocalVariable> argument = new ( func.rhs.argumentVariables );
                    List<LocalVariable> parameter = new ( func.rhs.function.parameters );

                    List<Expression> precondition = new ( func.rhs.function.entryLocation.conditions );


                    for (int j = 0; j < argument.Count; j++)
                    {
                        for (int k = 0; k < precondition.Count; k++)
                        {
                            precondition [ k ] = precondition [ k ].Substitute ( parameter [ j ],
                                new VariableExpression ( argument [ j ] ) );
                        }
                    }
                    current_path.tailConditions = precondition;
                    BasicPath tmp_path = Copy_path ( current_path );

                    List<Expression> rank = new ( func.rhs.function.entryLocation.rankingFunctions );
                    for (int k = 0; k < rank.Count; k++)
                    {
                        for (int p = 0; p < argument.Count; p++)
                        {
                            rank [ k ] = rank [ k ].Substitute ( parameter [ p ], new VariableExpression ( argument [ p ] ) );
                        }
                    }
                    tmp_path.tailRankingFunctions = new List<Expression> ( rank );
                    basic_paths.Add ( tmp_path );


                    //第二条路径，过程调用执行后的基本路径  
                    List<LocalVariable> new_val = new ( func.lhs );
                    List<LocalVariable> return_val = new ( func.rhs.function.rvs );
                    List<Expression> post_condition = new ( func.rhs.function.exitLocation.conditions );
                    for (int j = 0; j < argument.Count; j++)
                    {
                        for (int k = 0; k < post_condition.Count; k++)
                        {
                            post_condition [ k ] = post_condition [ k ].Substitute ( parameter [ j ], new VariableExpression ( argument [ j ] ) );
                        }

                    }
                    for (int j = 0; j < return_val.Count; j++)
                    {
                        for (int k = 0; k < post_condition.Count; k++)
                        {
                            post_condition [ k ] = post_condition [ k ].Substitute ( return_val [ j ], new VariableExpression ( new_val [ j ] ) );
                        }
                    }

                    AssumeStatement assume_statement = new ();
                    List<Expression> new_post_condition = new ( post_condition );
                    assume_statement.condition = Merge_expression ( new_post_condition );
                    current_path.statements.Add ( assume_statement );
                }
                else
                {
                    //其他情况直接添加statement
                    current_path.statements.Add ( current_statement );
                }
            }
            return flag_;
        }


        // 验证条件计算
        public static Expression Cal_verification_condition ( BasicPath path )
        {
            Expression wp = Merge_expression ( path.tailConditions );
            Expression headcondition = Merge_expression ( path.headConditions );
            //只剩赋值和assume
            for (int i = path.statements.Count - 1; i >= 0; i--)    
            {
                Statement statement = path.statements [ i ];
                // 赋值
                if (statement is VariableAssignStatement assign_statement)
                {
                    wp = wp.Substitute ( assign_statement.variable, assign_statement.rhs );
                }
                else if (statement is SubscriptAssignStatement subscript_statement)
                {
                    VariableExpression len = new ( subscript_statement.array.length );
                    VariableExpression array = new ( subscript_statement.array );
                    ArrayUpdateExpression exp = new ( array, subscript_statement.subscript, 
                        subscript_statement.rhs, len );
                    wp = wp.Substitute ( subscript_statement.array, exp );
                }
                // assume
                else if (statement is AssumeStatement assume_statement)
                {
                    wp = new ImplicationExpression ( assume_statement.condition, wp );  
                }
            }
            // 合并成φ ==> φ'的形式
            ImplicationExpression res = new ( headcondition, wp );
            return res;
        }
        
        public Expression Cal_wp_for_rank(List<Expression> headrank, List<Expression> tailrank, 
            Dictionary<LocalVariable, LocalVariable> name, BasicPath path)
        {
            foreach (var item in name)
            {
                for (int k = 0; k < headrank.Count; k++)
                {
                    VariableExpression exp = new ( item.Value );
                    headrank [ k ] = headrank [ k ].Substitute ( item.Key, exp );
                }
            }

            Expression condition = new GTExpression ( headrank [ 0 ], tailrank [ 0 ] );
            for (int i = 1; i < headrank.Count; i++)
            {
                Expression subCondition = new EQExpression ( headrank [ 0 ], tailrank [ 0 ] );
                for (int j = 1; j <= i; j++)
                {
                    if (j < i)
                    {
                        subCondition = new AndExpression ( subCondition, new EQExpression ( headrank [ j ], tailrank [ j ] ) );
                    }
                    else
                    {
                        subCondition = new AndExpression ( subCondition, new GTExpression ( headrank [ j ], tailrank [ j ] ) );
                    }
                }
                condition = new OrExpression ( condition, subCondition );
            }

            // wp
            BasicPath tmp_path = Copy_path ( path );
            List<Expression> explist = new ();
            explist.Add ( condition );
            tmp_path.tailConditions = new List<Expression> ( explist );
            Expression precondition = Cal_verification_condition ( tmp_path );

            // 替换回来
            foreach (var item in name)
            {
                precondition = precondition.Substitute ( item.Value, new VariableExpression ( item.Key ) );
            }
            return precondition;
        }

        // 秩函数处理
        bool Verify_rank ( BasicPath path )
        {

            if (path.headRankingFunctions.Count > 0 && path.tailRankingFunctions.Count > 0) 
            {
                //System.Console.Write ( "进入verify_rank\n" );
                List<Expression> headrank = new ( path.headRankingFunctions );
                List<Expression> tailrank = new ( path.tailRankingFunctions );

                Dictionary<LocalVariable, LocalVariable> name = new ();
                foreach (Expression headRankingFunction in headrank)
                {
                    HashSet<LocalVariable> variables = headRankingFunction.GetFreeVariables ();
                    foreach (LocalVariable var in variables)
                    {
                        bool contain_key = name.ContainsKey ( var );
                        //System.Console.Write ( contain_key );
                        //System.Console.WriteLine();
                        if (!contain_key)
                        {
                            LocalVariable variable = new ();
                            variable.name = "new_" + var.name;
                            variable.type = var.type;
                            name.Add ( var, variable );
                        }
                    }
                }

                // 准备计算wp
                Expression precondition =  Cal_wp_for_rank ( headrank, tailrank, name, path );

                //检验
                if (solver.CheckValid ( precondition ) != null)
                {
                    return false;
                }
            }

            if (path.headRankingFunctions.Count > 0)         
            {
                List<Expression> headrank = new ( path.headRankingFunctions );
                Expression precondition = Merge_expression ( path.headConditions );
                IntConstantExpression zero = new ( 0 );
                Expression exp = new GEExpression ( headrank [ 0 ], zero );
                for (int j = 1; j < headrank.Count; j++)
                {
                    Expression tmp = new GEExpression ( headrank [ j ], zero );
                    List<Expression> tmp1 = new ();
                    tmp1.Add ( tmp );
                    exp = Merge_expression ( tmp1 );
                }
                ImplicationExpression test = new ( precondition, exp );
                if (solver.CheckValid ( test ) != null)
                {
                    return false;
                }
            }
            return true;
        }

        

        // 基本路径计算
        public void Generate_basic_path ( BasicPath current_path, Location location )
        {
            List<BasicPath> assumePath = new ();
            
            bool flag_ = false;

            // 遍历后继
            flag_ = Scan_post(current_path, location, assumePath);

            //当前语句遍历完
            int assumeindex = 0;
            foreach (Location next_location in location.succLocations)
            {
                if (flag_)
                {
                    Location tmp_location = (Location)next_location;
                    BasicPath path = Copy_path ( assumePath [ assumeindex ] );
                    assumeindex++;
                    Generate_basic_path ( path, tmp_location );
                }
                else if (next_location is ExitLocation exit_loaction)
                {
                    current_path.tailConditions = exit_loaction.conditions;
                    BasicPath path = Copy_path ( current_path );
                    basic_paths.Add ( path );
                }
                else if (next_location is LoopHeadLocation loophead_location)
                {
                    current_path.tailConditions = loophead_location.invariants;
                    BasicPath path = Copy_path ( current_path );
                    if (loophead_location.rankingFunctions.Count != 0)                                                                             //添加秩函数
                    {
                        path.tailRankingFunctions = new List<Expression> ( loophead_location.rankingFunctions );
                    }
                    basic_paths.Add ( path );

                    bool contain_key = loop_cache.ContainsKey ( loophead_location );
                    //进入循环
                    if (!contain_key)
                    {
                        loop_cache.Add ( loophead_location, true );

                        BasicPath new_path = new ();
                        new_path.headConditions = new List<Expression> ( loophead_location.invariants );

                        if (loophead_location.rankingFunctions.Count != 0)                                                                             //添加秩函数
                        {
                            new_path.headRankingFunctions = new List<Expression> ( loophead_location.rankingFunctions );
                        }
                        Generate_basic_path ( new_path, loophead_location );
                    }
                }
                else if (next_location is Location loc)
                {
                    BasicPath path = Copy_path ( current_path );
                    Generate_basic_path ( path, loc );
                }
            }

        }


        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public int Apply ( IRMain cfg )
        {
            // 投入谓词
            foreach (Predicate p in cfg.predicates)
            {
                solver.definePredicate ( p );
            }
            // 生成基本路径
            foreach (Function f in cfg.functions)   
            {
                BasicPath current_path = new ();
                current_path.headConditions = f.entryLocation.conditions;

                // 有秩函数
                //System.Console.Write ( "count:" + f.entryLocation.rankingFunctions.Count + '\n' );
                if (f.entryLocation.rankingFunctions.Count != 0)
                {
                    //System.Console.Write(current_path.headRankingFunctions);
                    current_path.headRankingFunctions = new List<Expression> ( f.entryLocation.rankingFunctions );
                }
                if (f.entryLocation.succLocations.Count == 0)
                {    
                    f.entryLocation.succLocations.Add ( f.exitLocation );
                }
                Generate_basic_path ( current_path, f.entryLocation );
            }


            // 验证条件
            for (int i = 0; i < basic_paths.Count; i++)
            {
                Expression verify = Cal_verification_condition ( basic_paths [ i ] );
                //System.Console.Write ( verify );
                //System.Console.WriteLine ();
                if (solver.CheckValid ( verify ) != null)
                {
                    return -1;
                }
            }

            //秩函数
            foreach (BasicPath path in basic_paths)
            {
                if (!Verify_rank(path))
                {
                    return -1;
                }
            }
            return 1;

        }
    }
}

