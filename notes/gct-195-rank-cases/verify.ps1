param(
  [Parameter(Mandatory=$true)][string]$LeanRoot
)
$ErrorActionPreference = 'Stop'
$LeanRoot = (Resolve-Path -LiteralPath $LeanRoot).Path
$build = Join-Path $PSScriptRoot '.build'
$mod = Join-Path $build 'PEqualNP/Gct'
New-Item -ItemType Directory -Force $mod | Out-Null
$oldPath = $env:LEAN_PATH
Push-Location $LeanRoot
try {
  $savedToolPath = $env:Path
  $env:Path = "$env:USERPROFILE\.elan\bin;$env:Path"
  $prefix = (& lake env lean --print-prefix | Out-String).Trim()
  if ($LASTEXITCODE) { throw 'Could not resolve the pinned Lean toolchain.' }
  $projectPath = (& lake env powershell -NoProfile -Command '[Console]::Write($env:LEAN_PATH)' | Out-String).Trim()
  if ($LASTEXITCODE) { throw 'Could not read the project Lean path.' }
  $env:LEAN_PATH = "$build;$projectPath"
  $lean = Join-Path $prefix 'bin/lean.exe'
  $modules = @(
    'QuarticEquality','ProfileFourSix','RankSeven','FourSixBound','FourierTable',
    'SaturatedTensorBound','OrderedPermanent','SaturatedMatrixBound','KernelTriples',
    'PermanentPencil','SaturatedKernel','DeskWords','DeskAlgebra','DeskPolarization',
    'DeskOrder','ChartTable','ChartSpan','ChartGradient','CanonicalCap','ReindexKernel',
    'RankSevenAssembly','RankSeven195','CubicSix','OneModeCubic','OneModeBound','CubicRankEightCase',
    'PureContractions','PureTests','PureRowEquations','PureGeometry','PureSixth','PureCriterion','PureRows195','QuotientWitness','QuotientWitness195'
  )
  foreach ($name in $modules) {
    $inputFile = Join-Path $PSScriptRoot "PEqualNP/Gct/$name.lean"
    & $lean -R $PSScriptRoot -o (Join-Path $mod "$name.olean") $inputFile
    if ($LASTEXITCODE) { throw "Lean failed on $name." }
  }
  $checker = Join-Path $LeanRoot '.lake/build/bin/checklemma.exe'
  & $checker PEqualNP.Gct.RankSeven195 (Join-Path $PSScriptRoot 'RankSeven195.txt') check
  if ($LASTEXITCODE) { throw 'The project checker did not accept the rank-seven statement.' }
  & $checker PEqualNP.Gct.CubicRankEightCase (Join-Path $PSScriptRoot 'CubicRankEightCase.txt') check
  if ($LASTEXITCODE) { throw 'The project checker did not accept the cubic statement.' }
  foreach ($name in 'PureRows195','QuotientWitness195') {
    & $checker "PEqualNP.Gct.$name" (Join-Path $PSScriptRoot "$name.txt") check
    if ($LASTEXITCODE) { throw "The project checker did not accept $name." }
  }
} finally {
  $env:Path = $savedToolPath
  $env:LEAN_PATH = $oldPath
  Pop-Location
}

