import {
    weierstrass
} from 'curves/abstract/weierstrass';
import {
    Field
} from 'curves/abstract/modular';
import {
    sha256
} from 'hashes/sha256'
import {
    hmac
} from 'hashes/hmac'
import {
    randomBytes
} from 'hashes/utils'
import { md5 } from 'js-md5'

const KCHARS = "BCDFGHJKMPQRTVWXY2346789";

const SPK_ECKEY = {
    "a": 1n,
    "b": 0n,
    "g": {
        "x": 10692194187797070010417373067833672857716423048889432566885309624149667762706899929433420143814127803064297378514651n,
        "y": 14587399915883137990539191966406864676102477026583239850923355829082059124877792299572208431243410905713755917185109n
    },
    "n": 629063109922370885449n,
    "p": 21782971228112002125810473336838725345308036616026120243639513697227789232461459408261967852943809534324870610618161n,
    "priv": 153862071918555979944n,
    "pub": {
        "x": 3917395608307488535457389605368226854270150445881753750395461980792533894109091921400661704941484971683063487980768n,
        "y": 8858262671783403684463979458475735219807686373661776500155868309933327116988404547349319879900761946444470688332645n
    }
};

const LKP_ECKEY = {
    "a": 1n,
    "b": 0n,
    "g": {
        "x": 18999816458520350299014628291870504329073391058325678653840191278128672378485029664052827205905352913351648904170809n,
        "y": 7233699725243644729688547165924232430035643592445942846958231777803539836627943189850381859836033366776176689124317n
    },
    "n": 675048016158598417213n,
    "p": 28688293616765795404141427476803815352899912533728694325464374376776313457785622361119232589082131818578591461837297n,
    "priv": 100266970209474387075n,
    "pub": {
        "x": 7147768390112741602848314103078506234267895391544114241891627778383312460777957307647946308927283757886117119137500n,
        "y": 20525272195909974311677173484301099561025532568381820845650748498800315498040161314197178524020516408371544778243934n
    }
};

function encodePkey(n) {
    if (typeof n !== 'bigint') throw new TypeError("n must be bigint");
    if (n < 0n) throw new Error("n is negative");
    if (n === 0n) return "";

    let out = "";
    let currentN = n;

    while (currentN > 0n) {
        const remainder = Number(currentN % 24n);
        out = KCHARS[remainder] + out;
        currentN = currentN / 24n;
    }

    out = out.padStart(35, KCHARS[0]);

    const segments = [];
    for (let i = 0; i < out.length; i += 5) {
        segments.push(out.substring(i, i + 5));
    }

    return segments.join("-");
}

function decodePkey(k) {
    const keyString = k.replaceAll("-", "");
    
    if (keyString.length % 5 !== 0) {
        throw new Error("Bad length");
    }
    
    let out = 0n;

    for (const char of keyString) {
        const value = KCHARS.indexOf(char);
        if (value === -1) {
            throw new Error(`Invalid character: ${char}`);
        }
        out = out * 24n + BigInt(value);
    }
    return out;
}

function bigIntToBytesLE(n, l) {
    if (typeof n !== 'bigint') throw new TypeError("n must be a bigint");
    if (n < 0n) {
        console.warn("n is negative, inverting");
        n = -n;
    }
    let hex = n.toString(16);

    if (hex.length % 2) {
        hex = '0' + hex;
    }

    const numBytes = hex.length / 2;
    let requiredLength = l;
    if (requiredLength === undefined || requiredLength === null) {
        requiredLength = numBytes === 0 ? 1 : numBytes;
    } else {
        requiredLength = Number(requiredLength);
        if (isNaN(requiredLength) || requiredLength < 0) {
            throw new Error("invalid length");
        }
    }

    const bytes = new Uint8Array(requiredLength);
    let j = 0;
    for (let i = hex.length - 2; i >= 0 && j < requiredLength; i -= 2) {
        bytes[j++] = parseInt(hex.substring(i, i + 2), 16);
    }

    if (l !== undefined && requiredLength > 0 && n >= (1n << (BigInt(requiredLength) * 8n))) {
        console.warn(`bigint ${n} too large for ${l} bytes, potential truncation`);
    }

    return bytes;
}

function bytesToBigIntLE(bytes) {
    if (!(bytes instanceof Uint8Array)) {
        throw new TypeError("input data must be a Uint8Array");
    }
    let value = 0n;
    for (let i = 0; i < bytes.length; i++) {
        value += BigInt(bytes[i]) << (8n * BigInt(i));
    }
    return value;
}

async function sha1(data) {
    if (!(data instanceof Uint8Array)) {
        throw new TypeError("input data must be a Uint8Array");
    }
    const hashBuffer = await crypto.subtle.digest('SHA-1', data);
    return new Uint8Array(hashBuffer);
}

async function md5Hash(data) {
    const hashArray = md5.array(data);
    return new Uint8Array(hashArray);
}

function rc4(keyBytes, dataBytes) {
    let s = new Uint8Array(256);
    for (let i = 0; i < 256; i++) {
        s[i] = i;
    }

    let j = 0;
    let i = 0;
    for (let i = 0; i < 256; i++) {
        j = (j + s[i] + keyBytes[i % keyBytes.length]) % 256;
        [s[i], s[j]] = [s[j], s[i]];
    }

    i = 0, j = 0;
    let resultBytes = new Uint8Array(dataBytes.length);
    for (let k = 0; k < dataBytes.length; k++) {
        i = (i + 1) % 256;
        j = (j + s[i]) % 256;
        [s[i], s[j]] = [s[j], s[i]];
        const t = (s[i] + s[j]) % 256;
        resultBytes[k] = dataBytes[k] ^ s[t];
    }
    return resultBytes;
}

const utf16leEncoder = {
    encode: (str) => {
        const buffer = new ArrayBuffer(str.length * 2);
        const view = new DataView(buffer);
        for (let i = 0; i < str.length; i++) {
            view.setUint16(i * 2, str.charCodeAt(i), true);
        }
        return new Uint8Array(buffer);
    }
};

function generateRandomBigInt(min, max) {
    if (typeof min !== 'bigint' || typeof max !== 'bigint') {
        throw new TypeError("min and max must be BigInts");
    }
    if (min >= max) {
        throw new Error("min must be strictly less than max");
    }
    const range = max - min;
    const bitsNeeded = BigInt(range.toString(2).length);
    const bytesNeeded = Number((bitsNeeded + 7n) / 8n);

    let randomBigInt;
    let attempts = 0;

    do {
        if (attempts++ > 100) throw new Error("lmao");

        const randomBytes = new Uint8Array(bytesNeeded);
        crypto.getRandomValues(randomBytes);

        let tempValue = 0n;
        for (let i = 0; i < randomBytes.length; i++) {
            tempValue = (tempValue << 8n) + BigInt(randomBytes[i]);
        }

        const mask = bitsNeeded === 0n ? 0n : (1n << bitsNeeded) - 1n;
        tempValue = tempValue & mask;

        randomBigInt = min + tempValue;
    } while (randomBigInt >= max);

    return randomBigInt;
}

function mod(n, m) {
    if (typeof n !== 'bigint' || typeof m !== 'bigint') {
        throw new TypeError("mod function requires BigInt args");
    }
    if (m <= 0n) throw new Error("modulus must be positive");
    const result = n % m;
    return result >= 0n ? result : result + m;
}

function concatBytes(...arrays) {
    const totalLength = arrays.reduce((acc, arr) => acc + arr.length, 0);
    const result = new Uint8Array(totalLength);
    let offset = 0;
    for (const arr of arrays) {
        if (!(arr instanceof Uint8Array)) throw new TypeError("arguments must be Uint8Arrays");
        result.set(arr, offset);
        offset += arr.length;
    }
    return result;
}

const hmacSha256 = (key, ...msgs) => {
    return hmac(sha256, key, concatBytes(...msgs));
};

function makeCurve(curveDef) {
    if (!curveDef || typeof curveDef !== 'object' ||
        typeof curveDef.p !== 'bigint' || typeof curveDef.n !== 'bigint' ||
        !curveDef.g || typeof curveDef.g.x !== 'bigint' || typeof curveDef.g.y !== 'bigint' ||
        !curveDef.pub || typeof curveDef.pub.x !== 'bigint' || typeof curveDef.pub.y !== 'bigint' ||
        typeof curveDef.a !== 'bigint' || typeof curveDef.b !== 'bigint') {
        throw new Error("Incomplete/invalid curve definition");
    }

    const Fp = Field(curveDef.p);

    const curve = weierstrass({
        a: curveDef.a,
        b: curveDef.b,
        Fp: Fp,
        n: curveDef.n,
        Gx: curveDef.g.x,
        Gy: curveDef.g.y,
        h: 1n,
        hash: sha256,
        hmac: hmacSha256,
        randomBytes
    });

    const Point = curve.ProjectivePoint;

    let G, K;
    try {
        G = Point.fromAffine({
            x: curveDef.g.x,
            y: curveDef.g.y
        });
        K = Point.fromAffine({
            x: curveDef.pub.x,
            y: curveDef.pub.y
        });
    } catch (error) {
        console.error("Error creating points from definition:", curveDef);
        throw new Error(`Failed to create curve points: ${error.message}`);
    }

    try {
        G.assertValidity();
        K.assertValidity();
    } catch (error) {
        throw new Error(`Curve point validation failed: ${error.message}`);
    }

    return {
        E: curve.CURVE,
        G: G,
        K: K
    };
}

let spkCurveData, lkpCurveData;
try {
    spkCurveData = makeCurve(SPK_ECKEY);
    lkpCurveData = makeCurve(LKP_ECKEY);
    console.log("ECC Curves initialized");
} catch (error) {
    console.error("Could not initialize ECC curves", error);

    document.getElementById('generateSpkBtn').disabled = true;
    document.getElementById('generateLkpBtn').disabled = true;
    document.getElementById('output').textContent = `初始化密码学工具包失败，错误是：${error.message}`;
}

function getSpkid(pid) {
    if (typeof pid !== 'string' || pid.length < 23) {
        throw new Error("Invalid PID");
    }

    const spkidStringPart1 = pid.substring(10, 16);
    const spkidStringPart2 = pid.substring(18, 23);
    const combinedSpkidString = spkidStringPart1 + spkidStringPart2;
    const spkidNumString = combinedSpkidString.split("-")[0];
    const spkidNum = parseInt(spkidNumString, 10);

    if (isNaN(spkidNum)) {
        throw new Error("Could not parse SPK ID number from PID");
    }
    return BigInt(spkidNum);
}

async function validateTskey(pid, tskey, isSpk = true) {
    try {
        const keydataInt = decodePkey(tskey);

        const keydataBytes = bigIntToBytesLE(keydataInt, 21n);

        const pidBytesUtf16le = utf16leEncoder.encode(pid);
        const md5Digest = await md5Hash(pidBytesUtf16le);
        const rk = concatBytes(md5Digest.slice(0, 5), new Uint8Array(11));

        const dc_kdata = rc4(rk, keydataBytes);

        if (dc_kdata.length < 21) {
            console.error("insufficient data length:", dc_kdata.length);
            return false;
        }

        const keydata_inner = dc_kdata.slice(0, 7);
        const sigdataBytes = dc_kdata.slice(7);

        const sigdata = bytesToBigIntLE(sigdataBytes);

        const h = sigdata & 0x7FFFFFFFFn;
        const s = (sigdata >> 35n) & 0x1FFFFFFFFFFFFFFFFFn;

        const curveData = isSpk ? spkCurveData : lkpCurveData;
        if (!curveData) throw new Error("Curve data not initialized");
        const {
            E,
            G,
            K
        } = curveData;

        const hK = K.multiply(h);
        const sG = G.multiply(s);
        const R = hK.add(sG);
        const R_affine = R.toAffine();

        const RxBytes = bigIntToBytesLE(R_affine.x, 48n);
        const RyBytes = bigIntToBytesLE(R_affine.y, 48n);

        const sha1Input = concatBytes(keydata_inner, RxBytes, RyBytes);
        const md = await sha1(sha1Input);

        const part1Bytes = md.slice(0, 4);
        const part2Bytes = md.slice(4, 8);
        const part1 = bytesToBigIntLE(part1Bytes);
        const part2Intermediate = bytesToBigIntLE(part2Bytes);
        const part2 = part2Intermediate >> 29n;
        const ht = (part2 << 32n) | part1;

        const hashCheck = (h === ht);

        if (!hashCheck) return false;

        if (isSpk) {
            const spkid_from_key = bytesToBigIntLE(keydata_inner) & 0x1FFFFFFFFFn;
            const spkid_from_pid = getSpkid(pid);

            const spkIdCheck = (spkid_from_key === spkid_from_pid);

            return spkIdCheck;
        } else {
            return true;
        }
    } catch (error) {
        console.error("Error during validation:", error);
        return false;
    }
}

async function generateTsKey(pid, keydata_inner, isSpk = true) {
    const params = isSpk ? SPK_ECKEY : LKP_ECKEY;
    const curveData = isSpk ? spkCurveData : lkpCurveData;
    if (!curveData) throw new Error("Curve data not initialized");
    const {
        E,
        G,
        K
    } = curveData;
    const privKey = params.priv;

    if (!(keydata_inner instanceof Uint8Array) || keydata_inner.length !== 7) {
        throw new Error("keydata_inner must be 7 bytes or uint8array");
    }

    const pidBytesUtf16le = utf16leEncoder.encode(pid);
    const md5Digest = await md5Hash(pidBytesUtf16le);
    const rk = concatBytes(md5Digest.slice(0, 5), new Uint8Array(11));

    let attempts = 0;
    const maxAttempts = 1000;

    // if (typeof E.n !== 'bigint') {
    //     throw new Error("test");
    // }

    while (attempts < maxAttempts) {
        attempts++;

        const c_nonce = generateRandomBigInt(1n, E.n);

        const R = G.multiply(c_nonce);
        const R_affine = R.toAffine();

        const RxBytes = bigIntToBytesLE(R_affine.x, 48n);
        const RyBytes = bigIntToBytesLE(R_affine.y, 48n);

        const sha1Input = concatBytes(keydata_inner, RxBytes, RyBytes);
        const md = await sha1(sha1Input);

        const part1 = bytesToBigIntLE(md.slice(0, 4));
        const part2Intermediate = bytesToBigIntLE(md.slice(4, 8));
        const part2 = part2Intermediate >> 29n;
        const h = (part2 << 32n) | part1;

        const s = mod(c_nonce - (privKey * h), E.n);

        const s_masked = s & 0x1FFFFFFFFFFFFFFFFFn;

        if (s_masked !== s || s_masked >= 0x1FFFFFFFFFFFFFFFFFn) {
            continue;
        }

        const h_masked = h & 0x7FFFFFFFFn;
        const sigdata = (s_masked << 35n) | h_masked;
        const sigdataBytes = bigIntToBytesLE(sigdata, 14n);

        const pkdata = concatBytes(keydata_inner, sigdataBytes);
        if (pkdata.length !== 21) {
            console.error("pkdata not 21 bytes long:", pkdata.length);
            continue;
        }

        const pke = rc4(rk, pkdata);

        const pk = bytesToBigIntLE(pke.slice(0, 20));
        const pkstr = encodePkey(pk);

        if (await validateTskey(pid, pkstr, isSpk)) {
            return pkstr;
        } else {
            console.warn(`Generated key ${pkstr} failed validation, retrying...`);

        }
    }

    throw new Error(`Failed to generate a valid key after ${maxAttempts} attempts.`);
}

async function generateSpk(pid) {
    const spkidNum = getSpkid(pid);

    const spkdata = bigIntToBytesLE(spkidNum, 7n);
    if (spkdata.length !== 7) throw new Error("SPKID did not convert to 7 bytes");

    return await generateTsKey(pid, spkdata, true);
}

async function generateLkp(pid, countInput, majorVerInput, minorVerInput, chidInput) {

    const count = BigInt(countInput);
    const majorVer = Number(majorVerInput);
    const minorVer = Number(minorVerInput);
    const chid = BigInt(chidInput);

    if (isNaN(majorVer) || isNaN(minorVer)) {
        throw new Error("Invalid Major/Minor version number");
    }

    let version = 1n;
    if ((majorVer === 5 && minorVer > 0) || majorVer > 5) {
        version = (BigInt(majorVer) << 3n) | BigInt(minorVer);
    }

    const lkpinfo = (chid << 46n) |
        (count << 32n) |
        (2n << 18n) |
        (144n << 10n) |
        (version << 3n);

    const lkpdata = bigIntToBytesLE(lkpinfo, 7n);
    if (lkpdata.length !== 7) throw new Error("LKP Info did not convert to 7 bytes");

    return await generateTsKey(pid, lkpdata, false);
}

const pidInput = document.getElementById('pid');
const countInput = document.getElementById('count');
const chidVerInput = document.getElementById('chidverselect');
const generateSpkBtn = document.getElementById('generateSpkBtn');
const generateLkpBtn = document.getElementById('generateLkpBtn');
const generateSpkFrm = document.getElementById('generateSpkFrm');
const generateLkpFrm = document.getElementById('generateLkpFrm');
const outputPre = document.getElementById('output');

function setLoading(button, isLoading) {
    if (isLoading) {
        button.disabled = true;
        button.textContent = '生成中……';
        outputPre.textContent = '正在处理……';
        outputPre.classList.remove('error');
        outputPre.classList.add('loading');
    } else {
        button.disabled = false;

        if (button.id === 'generateSpkBtn') button.textContent = '生成许可证服务器ID（SPK）';
        if (button.id === 'generateLkpBtn') button.textContent = '生成许可证密钥包（LKP）';
        outputPre.classList.remove('loading');
    }
}

generateSpkFrm.addEventListener('submit', async () => {
    const pid = pidInput.value.trim();
    if (!pid) {
        outputPre.textContent = '错误：产品ID（PID）是必需的。';
        outputPre.classList.add('error');
        return;
    }

    if (!/^\d{5}-\d{5}-\d{5}-[A-Z]{2}\d{3}$/i.test(pid) && !/^\d{5}-OEM-\d{7}-\d{5}$/i.test(pid) && !/^\d{5}-\d{3}-\d{7}-\d{5}$/i.test(pid)) {
        console.warn("PID format doesn't strictly match common patterns, but attempting anyway:", pid);
    }

    setLoading(generateSpkBtn, true);
    try {
        const spk = await generateSpk(pid);
        outputPre.textContent = spk;
        outputPre.classList.remove('error');
    } catch (error) {
        console.error("SPK Generation Error:", error);
        outputPre.textContent = `生成许可证服务器ID（SPK）时出错：${error.message}`;
        outputPre.classList.add('error');
    } finally {
        setLoading(generateSpkBtn, false);
    }
});

generateLkpFrm.addEventListener('submit', async () => {
    const pid = pidInput.value.trim();
    const countStr = countInput.value.trim();
    const chidVerStr = chidVerInput.value.trim();

    if (!pid || !countStr || !chidVerStr) {
        outputPre.textContent = '错误：生成许可证密钥包（LKP）需要产品ID（PID）、数量、许可证类型和许可证版本。';
        outputPre.classList.add('error');
        return;
    }

    if (!/^\d{5}-\d{5}-\d{5}-[A-Z]{2}\d{3}$/i.test(pid) && !/^\d{5}-OEM-\d{7}-\d{5}$/i.test(pid) && !/^\d{5}-\d{3}-\d{7}-\d{5}$/i.test(pid)) {
        console.warn("PID format doesn't strictly match common patterns, but attempting anyway:", pid);

    }

    const chidVerMatch = chidVerStr.match(/^(\d+)_(\d+)_(\d+)$/);
    if (!chidVerMatch) {
        outputPre.textContent = '错误：CHID 和版本必须采用 CHID_主版本_次版本 格式（例如，001_5_0）。';
        outputPre.classList.add('error');
        return;
    }
    const [, chidStr, majorVerStr, minorVerStr] = chidVerMatch;

    let count, majorVer, minorVer, chid;
    try {
        count = parseInt(countStr, 10);
        majorVer = parseInt(majorVerStr, 10);
        minorVer = parseInt(minorVerStr, 10);
        chid = parseInt(chidStr, 10);

        if (isNaN(count) || count < 1 || isNaN(majorVer) || majorVer < 0 || isNaN(minorVer) || minorVer < 0 || isNaN(chid) || chid < 0) {
            throw new Error("Count, Version parts, and CHID must be valid non-negative numbers (Count >= 1).");
        }
        BigInt(count);
        BigInt(chid);

    } catch (e) {
        outputPre.textContent = `错误：无效的数字输入：${e.message}`;
        outputPre.classList.add('error');
        return;
    }

    setLoading(generateLkpBtn, true);
    try {
        const lkp = await generateLkp(pid, count, majorVer, minorVer, chid);
        outputPre.textContent = lkp;
        outputPre.classList.remove('error');
    } catch (error) {
        console.error("LKP Generation Error:", error);
        outputPre.textContent = `生成许可证密钥包（LKP）时出错：${error.message}`;
        outputPre.classList.add('error');
    } finally {
        setLoading(generateLkpBtn, false);
    }
});

outputPre.textContent = '请输入上方的详细信息并点击其中一个“生成”按钮。';