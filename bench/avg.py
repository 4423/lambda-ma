import pandas as pd
import glob
import xarray as xr

ds = []
for file in glob.glob("result*.txt"):
    d = pd.read_table(file, header=None, engine='python', index_col=0)
    ds.append(d.to_xarray())
da = xr.concat(ds, dim='dataset')
mean_df = da.mean(dim='dataset').to_dataframe()

mean_df.to_csv('result.txt', sep='\t', header=False, float_format='%.6f')