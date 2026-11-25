[CmdletBinding()]
param([switch]$Push)

$ErrorActionPreference = 'Stop'
$repositoryName = 'odd-zeta-five-lean'
$sizeLimit = 50MB

function Invoke-Checked {
    param([string]$Program, [string[]]$Arguments)
    & $Program @Arguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Program exited with code $LASTEXITCODE."
    }
}

Push-Location (Split-Path -Parent $PSScriptRoot)
try {
    $required = @(
        'README.md', '.gitignore', 'lakefile.toml', 'lake-manifest.json',
        'lean-toolchain', 'CITATION.cff', '.github/workflows/ci.yml',
        'OddZetaFive.lean', 'OddZetaFiveAudit.lean', 'verify-certificate.py',
        'b40a/certificate.json', 'paper/odd_zeta_five_b40a.pdf'
    )
    foreach ($path in $required) {
        if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
            throw "Required release file is missing: $path"
        }
    }
    if (-not (Test-Path -LiteralPath '.git')) {
        Invoke-Checked git @('init', '-b', 'main')
    }
    if ((Invoke-Checked git @('rev-parse', '--show-prefix')) -or
        (Invoke-Checked git @('branch', '--show-current')) -ne 'main') {
        throw 'Run this script in the extracted release with main checked out.'
    }

    $ignoredTracked = @(Invoke-Checked git @('ls-files', '-ci', '--exclude-standard'))
    if ($ignoredTracked.Count) {
        throw "The index already contains ignored paths: $($ignoredTracked -join ', ')"
    }
    $rootFiles = @(
        '.gitattributes', '.gitignore', 'CITATION.cff', 'LICENSE', 'README.md',
        'OddZetaFive.lean', 'OddZetaFiveAudit.lean', 'lake-manifest.json',
        'lakefile.toml', 'lean-toolchain', 'verify-certificate.py'
    )
    $candidates = @(Invoke-Checked git @('ls-files', '--cached', '--others', '--exclude-standard'))
    foreach ($path in $candidates) {
        if ($path -notmatch '^[A-Za-z0-9_.\/-]+$' -or
            ($path -notin $rootFiles -and
             $path -cnotmatch '^(?:\.github|OddZetaSix|PNTDependency|b40a|paper|reports|scripts)/')) {
            throw "Unexpected release path: $path"
        }
        $file = Get-Item -Force -LiteralPath $path
        if ($file.PSIsContainer -or ($file.Attributes -band [IO.FileAttributes]::ReparsePoint)) {
            throw "Expected a regular file: $path"
        }
        if ($file.Length -ge $sizeLimit) {
            throw "File is at or above the 50 MiB preflight limit: $path"
        }
    }

    # Apply the repository's LF normalization for this staging operation.
    Invoke-Checked git @('-c', 'core.safecrlf=false', 'add', '--all', '--', '.')
    $staged = @(Invoke-Checked git @('ls-files', '--stage'))
    foreach ($entry in $staged) {
        if ($entry -notmatch '^100(?:644|755) [0-9a-f]+ 0\t') {
            throw "Unexpected Git index entry: $entry"
        }
    }
    $indexedPaths = @(Invoke-Checked git @('ls-files'))
    foreach ($path in $required) {
        if ($path -cnotin $indexedPaths) {
            throw "Release file did not enter the index: $path"
        }
    }
    $blobIds = @($staged | ForEach-Object { ($_ -split ' ')[1] })
    $blobSizes = @($blobIds | git cat-file '--batch-check=%(objecttype) %(objectsize)')
    if ($LASTEXITCODE -ne 0 -or $blobSizes.Count -ne $staged.Count) {
        throw 'Could not read the staged blob sizes.'
    }
    foreach ($line in $blobSizes) {
        if ($line -notmatch '^blob ([0-9]+)$' -or [long]$Matches[1] -ge $sizeLimit) {
            throw "Invalid or oversized staged blob: $line"
        }
    }
    Write-Host "Preflight passed for $($staged.Count) files. Limit: 50 MiB per file."
    if (-not $Push) {
        Write-Host 'Review the index with git diff --cached --stat. Use -Push to publish main.'
        return
    }

    Invoke-Checked gh @('auth', 'status', '--hostname', 'github.com')
    $owner = Invoke-Checked gh @('api', '--hostname', 'github.com', 'user', '--jq', '.login')
    if ($owner -notmatch '^[A-Za-z0-9-]+$') {
        throw 'Could not determine the authenticated GitHub owner.'
    }
    $repo = "$owner/$repositoryName"
    $remoteUrl = "https://github.com/$repo.git"
    $remotes = @(Invoke-Checked git @('remote'))
    if ($remotes.Count) {
        if ($remotes.Count -ne 1 -or $remotes[0] -cne 'origin' -or
            (Invoke-Checked git @('remote', 'get-url', '--push', 'origin')) -ne $remoteUrl) {
            throw "Expected no remote or origin set to $remoteUrl."
        }
        if ((Invoke-Checked gh @('repo', 'view', "github.com/$repo", '--json', 'visibility', '--jq', '.visibility')) -cne 'PUBLIC') {
            throw "The existing origin must be public: $repo"
        }
    }

    git rev-parse --verify --quiet HEAD | Out-Null
    if ($LASTEXITCODE -eq 0) {
        if ((Invoke-Checked git @('rev-list', '--count', 'main')) -ne '1' -or
            (Invoke-Checked git @('write-tree')) -ne (Invoke-Checked git @('rev-parse', 'HEAD^{tree}'))) {
            throw 'A retry requires the same single initial commit. Start from a clean extraction for a new release repository.'
        }
    } else {
        Invoke-Checked git @('commit', '-m', 'Release B40a formalization v1.0.0')
    }
    if (-not $remotes.Count) {
        Invoke-Checked gh @('repo', 'create', $repo, '--public')
        Invoke-Checked git @('remote', 'add', 'origin', $remoteUrl)
    }
    Invoke-Checked git @(
        '-c', 'credential.helper=', '-c', 'credential.helper=!gh auth git-credential',
        'push', '--set-upstream', 'origin', 'main'
    )
    Invoke-Checked gh @('repo', 'edit', "github.com/$repo", '--default-branch', 'main')
    Write-Host "Pushed https://github.com/$repo"
    Write-Host "Check CI at https://github.com/$repo/actions/workflows/ci.yml"
} finally {
    Pop-Location
}
