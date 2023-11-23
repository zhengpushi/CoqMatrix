
* 介绍
  这里都是基于记录的非依赖类型的矩阵模型
  
* 几种模型
  * HighDimMatrix.v
	任意维度的矩阵，数据保存在一维列表中，只操纵形状和索引。
  * Matrix2D_Mat2Vec.v
	二维矩阵，先有Mat，然后定义出 cvec := mat n 1,  rvec := mat 1 n
  * Matrix2D_Vec2Mat.v
	二维矩阵，先有vec, 然后定义出 mat := vec (vec A)。理论上也可以得到高维矩阵。
